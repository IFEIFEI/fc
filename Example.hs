import Data.Char

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
