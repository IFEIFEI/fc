{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# language DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Char
import Data.Kind
import Data.Typeable
import Debug.Trace
import GHC.Generics
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Free
import Control.Comonad.Cofree

import Classes
import Combinator
import Components
import TypeLogic

data Incr t = Incr Int t
data Recall t = Recall (Int -> t)
data Clear t = Clear t

deriving instance Functor Incr
deriving instance Functor Recall
deriving instance Functor Clear

class (Functor sub,Functor sup) => sub :<: sup where
    inj :: sub a -> sup a
instance Functor f => f :<: f where
    inj = id
instance (Functor f, Functor g) => f :<: (f :+: g) where
    inj = L1
instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
    inj = R1 . inj

inject :: (g :<: f) => g (Free f a) -> Free f a
inject = Free . inj

incr :: (Incr :<: f) => Int -> Free f ()
incr i = inject (Incr i (return ()))

recall :: (Recall :<: f) => Free f Int
recall = inject (Recall return)

clear :: (Clear :<: f) => Free f ()
clear = inject (Clear (return ()))

type MemOp =  Incr :+: Recall :+: Clear


-- op = incr i op | recall (t -> op) | clear op
-- memop :: Parser (Free MemOp a)
-- memop = do {string "clear"; return clear }
--         +++ do { string "recall"; return recall }
--         +++ do { _ <- string "incr"; x <- number; return $ incr x}
--
-- number :: Parser Int
-- number = do { ns <- many1 digit1; return $ foldl (\x y-> x*10 + y) 0 ns}
-- digit1 = do { x <- token (sat isDigit); return $  (ord x - ord '0')}


tick :: Free MemOp Int     -- Pure () | Incr 1 (Free Incr ()) :: Free Incr ()
tick = do
        y <- recall
        clear
        incr 1
        incr 1
        return y

-- peekNum :: Free MemOp Int
-- peekNum = do {y <- recall; return y}

newtype Mem = Mem Int deriving (Show)
mapMem :: (Int -> Int) -> Mem -> Mem
mapMem f (Mem x) = Mem (f x)
runMem :: Mem -> Int
runMem (Mem m) = m

newtype CoIncr a = CoIncr (Int -> a) deriving (Functor)
newtype CoRecall a = CoRecall (Int, a) deriving (Functor)
newtype CoClear a = CoClear a deriving (Functor)

-- infixr 6 :@:
-- data (f :: k -> Type) (:@:)  (g :: k -> Type) a = f a :@: a
-- newtype Fix f = In (f (Fix f)) -- 单不动点
-- data Fix f g = FIn (f (Fix f g)) (g (Fix f g))
-- -- data Functor f g => CoIntp f a = CoIntp  (f a)
--  f a :*: g a :*: k a
--  f a :*: r g k a

type CoMemIntp = CoIncr :*: CoRecall :*: CoClear
type LinkCoMemIntp = (CoIncr :*: Incr) :*: (CoRecall :*: Recall) :*: (CoClear :*: Clear)
-- coIncr :: Monad m => m Mem -> Int -> m Mem
-- coIncr m x = do { z <- m ; return $ mapMem (\t -> t + x) z}
-- coRecall :: Monad m => m Mem -> m (Int, Mem)
-- coRecall m = do { x <- m ; return (runMem x, x) }
-- coClear :: Monad m => m Mem -> m Mem
-- coClear _ = return $ Mem 0
coIncr :: Mem -> Int -> Mem
coIncr m x = mapMem (\t -> t + x) m
coRecall :: Mem -> (Int, Mem)
coRecall m = (runMem m, m)
coClear :: Mem -> Mem
coClear _ = Mem 0

interpretMem :: Mem -> Cofree CoMemIntp Mem
interpretMem mem = coiter next start
                    where
                        next s = (CoIncr $ coIncr s) :*: (CoRecall $ coRecall s) :*: (CoClear $ coClear s)
                        start = mem
-- a :< (coiter psi <$> psi a) Free Incr ()


invLProd :: (Functor f, Functor g) => (f :*: g) a -> f a
invLProd (fa :*: _) = fa
invRProd :: (Functor f, Functor g) => (f :*: g) a -> g a
invRProd (_ :*: ga) = ga

instance (Functor f, Functor g) => (f :*: g) :<: f where
    inj = invLProd
instance (Functor f, Functor g, Functor h, g :<: f) => (h :*: g) :<: f  where
    inj = inj . invRProd

type family PairPred (f :: * -> *) (g :: * -> *) :: * where
    PairPred Identity Identity = HTrue
    PairPred ((->) a) ((,) a) = HTrue
    PairPred ((,) a) ((->) a) = HTrue
    PairPred f (g :+: k) = And (CastHTrue (PairPred f g)) (CastHTrue (PairPred f k))
    PairPred (f :*: h) k = Or (CastHTrue (PairPred f k))  (CastHTrue (PairPred h k))
    PairPred (Cofree f) (Free g) = HTrue
    -- type instance PairPred CoIncr Incr = HTrue
    -- type instance PairPred CoRecall Recall = HTrue
    -- type instance PairPred CoClear Clear = HTrue
    PairPred CoIncr Incr = HTrue
    PairPred CoRecall Recall = HTrue
    PairPred CoClear Clear = HTrue
    PairPred f g = HFalse

class (Functor f, Functor g) => Pairing f g where
    pair :: (a -> b -> r) -> f a -> g b -> r

class (Functor f, Functor g) => Pairing' flag f g where
    pair' :: flag -> (a -> b -> r) -> f a -> g b -> r

instance (Functor f, Functor g, PairPred f g ~ flag, Pairing' flag f g) => Pairing f g where
    pair = pair' (undefined::flag)

instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => Pairing' HFalse f g where
    pair' _ _ _ _ = error "No pair method"
instance {-# OVERLAPs #-} Pairing' HTrue Identity Identity where
    pair' _ f (Identity a) (Identity b) = trace "Pairing Identity Identity" f a b
instance {-# OVERLAPs #-} Pairing' HTrue ((->) a) ((,) a) where
    pair' _ p f = trace "Pairing ((->) a) ((,) a)" uncurry (p . f)
instance {-# OVERLAPs #-} Pairing' HTrue ((,) a) ((->) a) where
    pair' _ p f g =  trace " Pairing ((,) a) ((->) a)" pair (flip p) g f
instance {-# OVERLAPs #-} Pairing f g => Pairing' HTrue (Cofree f) (Free g) where
    pair' _ p (a :< _ ) (Pure x)  = trace "CF PURE" p a x
    pair' _ p (_ :< fs) (Free gs) = trace "CF FREE" pair (pair p) fs gs
instance {-# OVERLAPs #-} (Pairing g f, Pairing g h) => Pairing' HTrue g (f :+: h) where
    pair' _ p g (L1 f) = trace "Pairing g ([f] :+: g)" $ pair p g f
    pair' _ p g (R1 h) = trace "Pairing g (f :+: [g])" $ pair p g h
instance {-# OVERLAPs #-} (Functor h, Or (CastHTrue (PairPred f g)) (PairPred h g) ~ HLTrue, Pairing f g) => Pairing' HLTrue (f :*: h) g where
    pair' _ p (f :*: h) g = trace "Pairing ([f] :*: h) g" $ pair p f g
instance {-# OVERLAPs #-} (Functor f, Or (PairPred f g) (CastHTrue (PairPred h g)) ~ HRTrue, Pairing h g) => Pairing' HRTrue (f :*: h) g where
    pair' _ p (f :*: h) g = trace "Pairing (f :*: [h]) g" $ pair p h g

-- class (Functor f, Functor g) => Pairing f g where
--     pair :: (a -> b -> r) -> f a -> g b -> r
--     cp :: Int -> f a -> g b -> Bool
--     cp i _ _ = trace (show i ++ ": default true") True
--
-- instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => Pairing f g where
--     pair _ fa gb = trace ("default instance " ) error "No such paring "
--     cp i _ _ = trace (show i ++ ": default instance cp") False
-- instance {-# OVERLAPs #-} Pairing Identity Identity where
--     pair f (Identity a) (Identity b) = trace "Pairing Identity Identity" f a b
-- instance {-# OVERLAPs #-} Pairing ((->) a) ((,) a) where
--     pair p f = trace "Pairing ((->) a) ((,) a)" uncurry (p . f)
-- instance {-# OVERLAPs #-} Pairing ((,) a) ((->) a) where
--     pair p f g =  trace " Pairing ((->) a) ((,) a)" pair (flip p) g f
-- instance {-# OVERLAPs #-} Pairing f g => Pairing (Cofree f) (Free g) where
--     pair p (a :< _ ) (Pure x)  = trace "CF PURE" p a x
--     pair p (_ :< fs) (Free gs) = trace "CF FREE" pair (pair p) fs gs
--     cp i (a :< _ ) (Pure x) =  trace (show i ++ ": Error! ") error "text"
--     cp i (_ :< fs) (Free gs) = trace (show i ++ ": cp CF = " ++ show (cp 0 fs gs)) cp (i+1) fs gs

-- instance (Pairing g f, Pairing k h) => Pairing (g :*: k) (f :+: h) where
--   -- pair p (g :*: _) (L1 f) = pair p g f
--   -- pair p (_ :*: k) (R1 h) = pair p k h
--   -- cp (g :*: _) (L1 f) = cp g f
--   -- cp (_ :*: k) (R1 h) = cp k h
-- instance {-# OVERLAPs #-} (Functor f, Functor h, Functor g) => Pairing g (f :+: h) where
--     pair p g (L1 f) = trace "Pairing g ([f] :+: g)" $ if cp 0 g f then pair p g f else error "No such paring "
--     pair p g (R1 h) = trace "Pairing g (f :+: [g])" $ if cp 0 g h then pair p g h else error "No such paring "
--     cp i g (L1 f) = cp (i+1) g f
--     cp i g (R1 h) = cp (i+1) g h
--
-- instance {-# OVERLAPs #-} (Functor f, Functor g, Functor k) => Pairing (g :*: k) f where
--     pair p (g :*: k) f = trace "Pairing (g :*: k) f" $ if cp 0 g f then trace "select left intp" pair p g f else trace "select right intp" pair p k f
--     cp i x f = case x of g :*: k ->  trace (show i ++ ": cp g*k f = " ++ show (cp 0 g f) ++ show (cp 0 k f)) $ (cp (i+1) k f) || (cp (i+2) g f)

-- instance {-# OVERLAPs #-} (Pairing g f, Functor k) => Pairing (g :*: k) f where
--     pair p (g :*: k) f = trace "Pairing (g :*: k) f" $ if cp 0 g f then trace "select left intp" pair p g f else trace "select right intp" pair p k f
--     cp i (g :*: k) f = trace (show i ++ ": cp g*k f = " ++ show (cp 0 g f) ++ show (cp 0 k f)) $ (cp (i+1) k f) || (cp (i+2) g f)
-- instance {-# OVERLAPs #-} (Pairing k f, Functor g) => Pairing (g :*: k) f where
--     pair p (g :*: k) f = trace "Pairing (g :*: k) f" $ if cp 0 g f then trace "select left intp" pair p g f else trace "select right intp" pair p k f
--     cp i (g :*: k) f = trace (show i ++ ": cp g*k f = " ++ show (cp 0 g f) ++ show (cp 0 k f)) $ (cp (i+1) k f) || (cp (i+2) g f)
--
-- instance {-# OVERLAPs #-} (Functor f, Functor g, Functor h, Functor k) => Pairing (g :*: k) (f :+: h) where
--   pair p (g :*: k) (L1 f) = trace "Pairing (g :*: k) ([f] :+: h)" $ if cp 0 g f then trace "pgf" pair p g f else trace "pkf" pair p k f
--   pair p k (R1 h) = trace "Pairing (g :*: k) (f :+: [h])" $ pair p k h
--   cp i g (L1 f) = cp (i+1) g f
--   cp i g (R1 h) = cp (i+1) g h

-- instance (Pairing g f, h :<: g, Functor k) => Pairing (k :*: h) f where
--     pair p (_ :*: h) f = pair p (inj h) f
-- -- instance (Pairing g f, Functor h) =>  Pairing (h :*: g) f where
-- --     pair p (_ :*: g) f = pair p g f
-- instance (Pairing g f, Pairing k h) => Pairing (g :*: k) (f :+: h) where
--       pair p (g :*: _) (L1 f) = pair p g f
--       pair p (_ :*: k) (R1 h) = pair p k h

-- instance (Pairing g f, f :<: (h :+: k), (m :*: n) :<: g) => Pairing (m :*: n) (h :+: k) where
--     pair p coprod prod = pair p (inj coprod) (inj prod)
--     pair p coprod (R1 f) = pair p (inj coprod) f

instance {-# OVERLAPs #-} Pairing' HTrue CoIncr Incr where
    pair' _ f (CoIncr i) (Incr x t) = f (i x) t
instance {-# OVERLAPs #-} Pairing' HTrue CoRecall Recall where
    pair' _ f (CoRecall r) (Recall c) = pair f r c
instance {-# OVERLAPs #-} Pairing' HTrue CoClear Clear where
    pair' _ f (CoClear a) (Clear b) = f a b

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldTerm pur imp (Pure x) = pur x
foldTerm pur imp (Free t) = imp (fmap (foldTerm pur imp) t)

class Functor f => Run f where
    runAlgebra :: f (Mem -> (a, Mem)) -> (Mem -> (a, Mem))

instance Run Incr where
    runAlgebra (Incr k r) (Mem i) = r (Mem (i+k))
instance Run Recall where
    runAlgebra (Recall r) (Mem i) = r i (Mem i)
instance Run Clear where
    runAlgebra (Clear r) (Mem i) = r (Mem 0)
instance (Run f, Run g) => Run (f :+: g) where
    runAlgebra (L1 r) = runAlgebra r
    runAlgebra (R1 r) = runAlgebra r

run :: Run f => Free f a -> Mem -> (a, Mem)
run = foldTerm (,) runAlgebra




s = Mem 0
c = (CoIncr $ coIncr s)
i = (CoIncr $ coIncr s) :*: (CoRecall $ coRecall s) :*: (CoClear $ coClear s)
lInt = Identity 1 :*: Identity 2
rInt = Identity 3
t = Incr 1 1































--
