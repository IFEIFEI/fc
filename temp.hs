{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
{-# language StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable, DeriveAnyClass, FlexibleContexts #-}

import Control.Monad.Free
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Functor.Classes
import Text.Show.Deriving
import Data.Foldable

data Expr = Add Expr Expr | Lit Int
    deriving (Show, Eq)

isAdd :: Expr -> Bool
isAdd e = case e of Add _ _ -> True; _ -> False

isLit :: Expr -> Bool
isLit e = case e of Lit _ -> True; _ -> False
makeBaseFunctor ''Expr
deriveShow1 ''ExprF
deriving instance Show a => Show (ExprF a)
deriving instance Eq a => Eq (ExprF a)

data Predicate a = Pred {check :: a -> Bool}
instance Show (Predicate a) where
    show _ = "< Predicate >"

type Pattern = Free ExprF (Predicate Expr)

match :: Pattern -> Expr -> Bool
match pat e = case pat of
    Pure p -> check p e
    Free t -> case (t, project e) of
        (AddF p1 p2, AddF e1 e2) ->
            match p1 e1 && match p2 e2
        (LitF x, LitF y) ->
            x == y
        _ -> False

type GPattern t = Free (Base t) (Predicate t)

gmatch :: Eq (Base t ()) => Recursive t => Foldable (Base t) => GPattern t -> t -> Bool
gmatch pat e = case pat of
    Pure p -> check p e
    Free tp -> let
        te = project e
        tag_tp = fmap (const ()) tp
        tag_te = fmap (const ()) te
        children_tp = toList tp
        children_te = toList te
        in
            tag_tp == tag_te && and (zipWith gmatch children_tp children_te)

pat1, pat2, pat3 :: Pattern
pat1 = Pure (Pred isLit)
pat2 = Free (AddF pat1 pat1)
pat3 = Free (AddF pat2 pat1)

e1, e2, e3 :: Expr
e1 = Lit 1
e2 = Add e1 (Lit 2)
e3 = Add e2 (Lit 3)

main :: IO ()
main = print "Hello"
