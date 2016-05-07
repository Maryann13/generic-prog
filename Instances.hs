{-# LANGUAGE StandaloneDeriving, TypeOperators, FlexibleInstances,
    UndecidableInstances, MultiParamTypeClasses, GADTs             #-}
module Instances where

import GenericUniverse

-- Instances for the classes declared in the 'GenericProg' module

instance Show a => Show (I a) where
    show (I x) = show x

instance Iso I a where
    to         = I
    from (I x) = x

instance Iso (K a) a where
    to         = K
    from (K x) = x

instance Ord a => Ord (I a) where
    (>)  (I x) (I y) = x >  y
    (<=) (I x) (I y) = x <= y

instance Show a => Show (K a b) where
    show (K x) = show x

instance (Eq a, Iso f a) => Eq (f a) where
    (==) x y = (from x) == (from y)

-- A Show instance for NP
deriving instance  All (Show `Compose` f) xs => Show (NP f xs)

-- A Show instance for NS
deriving instance  All (Show `Compose` f) xs => Show (NS f xs)

-- A Show instance for SOP
deriving instance (Show (NS (NP f) xss)) => Show (SOP f xss)
