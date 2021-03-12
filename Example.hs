{-# language TemplateHaskell #-}
{-# language DeriveFunctor #-}
{-# language StandaloneDeriving #-}

import Data.Char
import Control.Monad.Free

import Classes
import Combinator
import Components

{-
expr ::= expr addop term | term
term ::= term mulop factor | factor
factor ::= digit | (expr)
digit ::= 0 | 1 | ... | 9
addop ::= + | -
mulop ::= * | /
-}
-- Parser Expr
{-
data Expr = Number Int | Add Expr Expr | Mul Expr Expr
            | Minus Expr Expr | Divide Expr Expr
    deriving (Show, Eq)
-}
data ExprF a = Number Int | Add a a | Mul a a
            | Minus a a | Divide a a

deriving instance Show a => Show (ExprF a)
deriving instance Eq a => Eq (ExprF a)
deriving instance Functor ExprF

newtype Fix f = In (f (Fix f))
type Expr a = Free ExprF a                   -- ( 对应嵌套不对  a fa ffa ffa fffa

-- （1 + 2） * 3
expr1 :: Fix (ExprF)
expr1 = In (Mul (In (Add (In (Number 1)) (In (Number 2)))) (In (Number 3)))

add,minus,mul,divide :: Int -> Int -> Expr Int
add x y = liftF $ Add x y
minus x y = liftF $ Minus x y
mul x y = liftF $ Mul x y
divide x y = liftF $ Divide x y

num :: Int -> Expr Int
num x = liftF $ Number x


expr2: Parser (Fix ExprF)

-- expr :: Parser (Fix ExprF)
-- addop :: Parser (ExprF Int)
-- mulop :: Parser (Int -> Int -> Int)

expr = term `chainl1` addop
term = factor `chainl1` mulop
factor = number +++ do {symb "("; n <- expr; symb ")"; return n }
number = do { ns <- many1 digit1; return $  (foldl (\x y-> x*10 + y) 0 ns)}
digit1 = do { x <- token (sat isDigit); return $  (ord x - ord '0')}

addop = do {symb "+"; return (+)} +++ do {symb "-"; return (-)}
mulop = do {symb "*"; return (*)} +++ do {symb "/"; return div}



























































--
