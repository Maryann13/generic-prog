{-# LANGUAGE PolyKinds, GADTs, ConstraintKinds, DataKinds,
    TypeOperators, TypeFamilies, RankNTypes, ScopedTypeVariables,
    MultiParamTypeClasses, UndecidableInstances, FlexibleInstances,
    FlexibleContexts                                                #-}
module GenericUniverse where

import GHC.Exts (Constraint)

-- N-ary product
data NP (f :: k -> *) (xs :: [k]) where
    Nil  :: NP f '[]
    (:*) :: f x -> NP f xs -> NP f (x ': xs)
infixr 5 :*

-- N-ary sum
data NS (f :: k -> *) (xs :: [k]) where
    Z ::    f x  -> NS f (x ': xs)
    S :: NS f xs -> NS f (x ': xs)

-- Isomorphous f a
class Iso f a where
    to   :: a   -> f a
    from :: f a -> a

-- Identity function on types
newtype I a = I {unI :: a}

-- A sum of products
newtype SOP f a = SOP {unSOP :: NS (NP f) a}
-- The representation of a datatype
type Rep f a = SOP f (Code a)

-- The class of representable datatypes
class (SListI (Code a), All SListI (Code a), All2 (Iso f) (Code a))
        => Generic (f :: * -> *) (a :: *) where
    type Code a :: [[*]]
    gfrom ::     f a -> Rep f a
    gto   :: Rep f a ->     f a

-- Constant function on types
newtype K a b = K {unK :: a}

{- Determines if a constraint holds for all
   elements of a type-level list            -}
type family All (c :: k -> Constraint) (xs :: [k])
        :: Constraint where
    All c '[]       = ()
    All c (x ': xs) = (c x, All c xs)

-- Requires a constraint for every element of a list of lists
type family All2 (c :: k -> Constraint) (xss :: [[k]])
        :: Constraint where
    All2 c '[]         = ()
    All2 c (xs ': xss) = (All c xs, All2 c xss)

{- For every list in a list of lists requires a constraint for
   its corresponding NP                                        -}
type family All_NP (c :: k -> Constraint) (f :: k -> *) (xss :: [[k]])
        :: Constraint where
    All_NP c f '[]         = ()
    All_NP c f (xs ': xss) = (c (NP f xs), All_NP c f xss)

-- Fixes the value of a type variable
data Proxy (a :: k) = Proxy

newtype (f -.-> g) a = Fn {apFn :: f a -> g a}
infixr 1 -.->

-- A natural number
data Nat = Zero | Suc Nat

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
fn_2 f = Fn (Fn . f)

-- Collapses an NP of Ks into a normal list
hcollapse :: NP (K a) xs -> [a]
hcollapse Nil         = []
hcollapse (K x :* xs) = x : hcollapse xs

-- Mapping over n-ary product
hmap :: (forall x . f x -> g x) -> NP f xs -> NP g xs
hmap _ Nil       = Nil
hmap m (x :* xs) = m x :* hmap m xs
