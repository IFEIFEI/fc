{-# language TemplateHaskell #-}
{-# language DeriveFunctor #-}

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
data Expr = Number Int | Add Expr Expr | Mul Expr Expr
            | Minus Expr Expr | Divide Expr Expr
    deriving (Show, Eq)
makeBaseFunctor ''Expr
deriveShow1 ''ExprF
deriving instance Show a => Show (ExprF a)
deriving instance Eq a => Eq (ExprF a)

expr :: Parser Int
addop :: Parser (Int -> Int -> Int)
mulop :: Parser (Int -> Int -> Int)

expr = term `chainl1` addop
term = factor `chainl1` mulop
factor = number +++ do {symb "("; n <- expr; symb ")"; return n}
number = do { ns <- many digit1; return $ foldl (\x y-> x*10 + y) 0 ns}
digit1 = do {x <- token (sat isDigit); return (ord x - ord '0')}

addop = do {symb "+"; return (+)} +++ do {symb "-"; return (-)}
mulop = do {symb "*"; return (*)} +++ do {symb "/"; return div}

type FExpr a = Free ExprF a

























































--
