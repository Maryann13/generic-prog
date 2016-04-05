{-# LANGUAGE PolyKinds, GADTs, ConstraintKinds, DataKinds,
    TypeOperators, TypeFamilies, RankNTypes, ScopedTypeVariables,
    StandaloneDeriving, MultiParamTypeClasses, UndecidableInstances,
    FlexibleInstances                                                #-}
module GenericProg where

import GHC.Exts (Constraint)

-- N-ary product
data NP (f :: k -> *) (xs :: [k]) where
    Nil  :: NP f '[]
    (:*) :: f x -> NP f xs -> NP f (x ': xs)
infixr 5 :*

-- Representable type f a
class Rep f a where
    from :: a   -> f a
    to   :: f a -> a

-- Identity function on types
newtype I a = I {unI :: a}

instance Show a => Show (I a) where
    show (I x) = show x

instance Rep I a where
    from x   = I x
    to (I x) = x

instance Ord a => Ord (I a) where
    (>)  (I x) (I y) = x > y
    (<=) (I x) (I y) = x <= y

-- Constant function on types
newtype K a b = K {unK :: a}

instance Show a => Show (K a b) where
    show (K x) = show x

instance (Eq a, Rep f a) => Eq (f a) where
    (==) x y = (to x) == (to y)

{- Determines if a constraint holds for all
   elements of a type-level list            -}
type family All (c :: k -> Constraint) (xs :: [k])
        :: Constraint where
    All c '[]       = ()
    All c (x ': xs) = (c x, All c xs)

-- Fixes the value of a type variable
data Proxy (a :: k) = Proxy

newtype (f -.-> g) a = Fn {apFn :: f a -> g a}
infixr 1 -.->

-- Singleton list: declaration
data SList (xs :: [k]) where
    SNil  :: SList '[]
    SCons :: SListI xs => SList (x ': xs)
class SListI (xs :: [k]) where
    sList :: SList xs

-- Singleton list: definition
instance SListI '[] where
    sList = SNil
instance SListI xs => SListI (x ': xs) where
    sList = SCons

-- Composition of type constructors
newtype (f :.: g) x = Comp {unComp :: f(g x)}

{- Definition for the special case of composition
   where the result is a Constraint               -}
class    (f (g x)) => (f `Compose` g) x
instance (f (g x)) => (f `Compose` g) x

deriving instance (All (Show `Compose` f) xs) => Show (NP f xs)

{- Produces an n-ary product of copies
   for constrained functions           -}
hcpure :: forall c f xs . (SListI xs, All c xs)
       => Proxy c -> (forall a . c a => f a) -> NP f xs
hcpure p x = case sList :: SList xs of
    SNil  -> Nil
    SCons -> x :* hcpure p x

{- Applies the list of functions pointwise
   to the list of arguments                -}
hap :: NP (f -.-> g) xs -> NP f xs -> NP g xs
hap Nil       Nil       = Nil
hap (f :* fs) (x :* xs) = apFn f x :* hap fs xs

fn_2 :: (f a -> f' a -> f'' a)
     -> (f -.-> f' -.-> f'') a
fn_2 f = Fn (\x -> Fn (\y -> f x y))

-- Collapses an NP of Ks into a normal list
hcollapse :: NP (K a) xs -> [a]
hcollapse Nil         = []
hcollapse (K x :* xs) = x : hcollapse xs

-- Mapping over n-ary product
hmap :: (forall x . f x -> g x) -> NP f xs -> NP g xs
hmap m Nil       = Nil
hmap m (x :* xs) = m x :* hmap m xs

-- Mapping of 2nd order with a constrained function
hcmap_2 :: All c xs
        => Proxy c
        -> (forall x . c x => f x -> g x -> h x)
        -> NP f xs -> NP (g -.-> h) xs
hcmap_2 p m Nil       = Nil
hcmap_2 p m (x :* xs) = (\x -> Fn (\y -> m x y)) x :* hcmap_2 p m xs
