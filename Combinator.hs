module Combinator where

import Data.Monoid
import Data.Char
import Data.Maybe
import Control.Monad (liftM)

import Classes

-- two ultities to operate the product type
map_snd :: (b -> c) -> (a, b) -> (a, c)
map_snd f x = (fst x, f.snd $ x)

map_fst :: (a -> c) -> (a, b) -> (c, b)
map_fst f x = (f.fst $ x, snd x)

-- simple parse to read a char
item :: Parser Char
item = Parser $ \inp -> case inp of
                                [] -> []
                                (x:xs) -> [(x,xs)]

-- apply p and q, gather the result, zero is the identity element
instance MonadZero Parser where
    zero = Parser $ \inp -> []
instance MonadPlus Parser where
    p +-+ q = Parser $ \inp -> (parse p inp) ++ (parse q inp)
(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser $ \inp -> case parse (p +-+ q) inp of
                                    [] -> []
                                    (x:xs) -> [x]

-- Parser a -> Parser b -> Parser (a * b)
-- Parser (a * b) !== Parser (b * a)
-- parse p, then apply q on the results, concate the parse result together
(<*>) :: Parser a -> Parser b -> Parser (a,b)
p <*> q = Parser $ \inp -> concat $ fmap pmap $  parse p inp
                        where
                            pmap = \(a,cs) -> fmap (\(b,xs)-> ((a,b),xs)) $ parse q cs
(<&>) :: Monoid a => Parser a -> Parser a -> Parser a
p <&> q = Parser $ \inp -> concat $ fmap pmap $ parse p inp
                        where
                            pmap = \(a,cs) -> fmap (\(b,xs)-> (mappend a b, xs)) $ parse q cs
pconcat :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pconcat f p q = Parser $ \inp -> concat $ fmap pmap $ parse p inp
                        where pmap = \(a,cs) -> fmap (\(b,xs)-> (f a b, xs)) $ parse q cs
-- Parser a -> Parser b -> Parser (a | b)
-- remember the result of which parser
(<|>) :: Parser a -> Parser b -> Parser (Either a b)
p <|> q = Parser $ \inp -> xs inp ++ ys inp
                            where
                                xs inp = fmap (\(a,xs)-> ((Left  a),xs)) $ parse p inp
                                ys inp = fmap (\(b,xs)-> ((Right b),xs)) $ parse q inp

-- try to use parser p, if succeed then stop, else try q
(<:>) :: Parser a -> Parser a -> Parser a
p <:> q = Parser $ \inp -> case parse p inp of
                            [] -> parse q inp
                            xs -> xs

orp :: (a -> c) -> (b -> c) -> Parser a -> Parser b -> Parser c
orp f g p q = Parser $ \inp -> case parse p inp of
                            [] -> fmap (\(c,cs)-> (g c, cs)) $ parse q inp
                            xs -> fmap (\(c,cs)-> (f c, cs)) xs

-- accept all the input string as a result
idp :: Parser String
idp = Parser $ \inp -> [(inp,"")]

sat :: (Char -> Bool) -> Parser Char
sat p = do {c <- item; if p c then return c else zero}

void_parser :: Parser ()
void_parser = Parser $ \inp -> [((), inp)]

-- try parse p zero or more times: p*
many :: Parser a -> Parser [a]
many p = many1 p +++ return []

-- get at least one result: p+
many1 :: Parser a -> Parser [a]
many1 p = do { a <- p; as <- many p; return (a:as)}

-- try to parse p n times: p[n]
manyn :: Int -> Parser a -> Parser [a]
manyn 0 _ = return []
manyn x p = do {a <- p; as <- manyn (x-1) p; return (a:as)}

-- try to parse p seperated by sep: p sep
sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

-- p (sep p)*
sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do a <- p
                    as <- many (do {sep; p})
                    return (a:as)
-- p || op (op (op p1 p2) p3) p4 ... || a
chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a
-- p || op (op (op p1 p2) p3) p4 ...
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do {a <- p; rest a}
                    where
                        rest a = (do f <- op
                                     b <- p
                                     rest (f a b)) +++ return a
-- a0 op1 a1 op2 a2 op3 a3 ...
-- op3 a3 (op2 a2 (op1 a1 a0))
foldparse :: Parser a -> Parser (a -> b -> b) -> Parser b -> Parser b
foldparse p op q = do {a <- q; rest a}
                        where
                            rest z = (do f <- op
                                         a <- p
                                         rest (f a z)) +++ return z

-- add an initial parse result
result :: a -> Parser a
result x = Parser $ \inp -> [(x, inp)]

-- modify the parse result
r_embeded, l_embeded :: Monoid a => a -> Parser a -> Parser a
l_embeded x p = do { xs <- p; return $ mappend x xs }
r_embeded x p = do { xs <- p; return $ flip mappend x xs }

remp :: Parser a -> Parser (a,String)
remp p = Parser $ \inp -> map (\(a,cs) -> ((a,pstr cs inp),cs)) $ parse p inp
                    where
                        pstr str inp = reverse $ take (length str) $ reverse inp
concat_remp :: Monoid a => Parser (a, String) -> Parser (a, String) -> Parser (a, String)
concat_remp p q = Parser $ \inp -> concatMap pmap $ parse p inp
                                where
                                    pmap = \(((c,cs), xs)) -> map (\((z,zs),ys) -> ((mappend c z, cs ++ zs) , ys) )  $ parse q xs

-- add xs to parser's input
put :: String -> Parser a -> Parser a
put xs p = Parser $ \inp -> fmap (\(c,cs) -> (c,xs ++ cs)) $ parse p inp

-- add xs to the end of a paser's input
put_back :: String -> Parser a -> Parser a
put_back xs p = Parser $ \inp -> parse p $ inp ++ xs

-- use p to parse a string without consuming any input
try :: Parser a -> Parser a
try p = Parser $ \inp -> fmap (\(a,_) -> (a, inp)) $ parse p inp

-- either success or failed
fail :: Parser a -> Parser (Maybe a)
fail p = Parser $ \inp -> let xs = parse p inp in
                            case xs of
                            [] -> [(Nothing, inp)]
                            _  -> fmap (\(a,_) -> (Just a, inp)) xs

-- transform the left input into another one
trans_input :: (String -> String) -> Parser a -> Parser a
trans_input f p = Parser $ \inp ->  fmap (\(a,_) -> (a, f inp)) $ parse p inp

-- change the parse result
map_result :: (a -> b) -> Parser a -> Parser b
map_result = fmap

-- drop n characters and go on parse
passn :: Int -> Parser a -> Parser a
passn n p = Parser $ \inp -> parse p $ drop n inp

-- parse a string in another direction
back_parse :: Parser a -> Parser a
back_parse p = Parser $ \inp -> fmap (\x -> map_snd reverse x) (parse p $ reverse inp)

-- Use monad to handle extra effect
toM :: Monad m => Parser a -> Parser (m a)
toM p = do {a <- p; return $ return a}

liftPM :: Monad m => (a -> b) -> Parser (m a) -> Parser (m b)
liftPM f p = do { a <- p; return $ liftM f a}

bindPM :: Monad m => (a -> m b) -> Parser (m a) -> Parser (m b)
bindPM f p = do { a <- p; return $ a >>= f}













--
