module Combinator where

import Data.Monoid
import Data.Char

import Classes

item :: Parser Char
item = Parser $ \inp -> case inp of
                                [] -> []
                                (x:xs) -> [(x,xs)]

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
(<*>) :: Parser a -> Parser b -> Parser (a,b)
p <*> q = Parser $ \inp -> concat $ fmap pmap $  parse p inp
                        where
                            pmap = \(a,cs) -> fmap (\(b,xs)-> ((a,b),xs)) $ parse q cs
-- Parser a -> Parser b -> Parser (a | b)
(<|>) :: Parser a -> Parser b -> Parser (Either a b)
p <|> q = Parser $ \inp -> xs inp ++ ys inp
                            where
                                xs inp = fmap (\(a,xs)-> ((Left  a),xs)) $ parse p inp
                                ys inp = fmap (\(b,xs)-> ((Right b),xs)) $ parse q inp

sat :: (Char -> Bool) -> Parser Char
sat p = do {c <- item; if p c then return c else zero}

many :: Parser a -> Parser [a]
many p = many1 p +++ return []

many1 :: Parser a -> Parser [a]
many1 p = do { a <- p; as <- many p; return (a:as)}

sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do a <- p
                    as <- many (do {sep; p})
                    return (a:as)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do {a <- p; rest a}
                    where
                        rest a = (do f <- op
                                     b <- p
                                     rest (f a b)) +++ return a
