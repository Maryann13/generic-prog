{-# LANGUAGE ConstraintKinds, TypeOperators, TypeFamilies,
    RankNTypes, FlexibleInstances, DataKinds               #-}
module Exercises where

import GenericProg

-- ------------------------------------------- Exercises
-- Checks lists for equality
heq :: All Eq xs => NP I xs -> NP I xs -> Bool
heq Nil         Nil         = True
heq (I x :* xs) (I y :* ys) = x == y && heq xs ys

-- Zips lists with a constrained function
hczipWith :: (All c xs, SListI xs)
          => Proxy c
          -> (forall a . c a => f a -> g a -> h a)
          -> NP f xs -> NP g xs -> NP h xs
hczipWith p f xs ys = hcpure p (fn_2 f) `hap` xs `hap` ys

hczipWith' :: All c xs
           => Proxy c
           -> (forall a . c a => f a -> g a -> h a)
           -> NP f xs -> NP g xs -> NP h xs
hczipWith' p f xs ys = hcmap_2 p f xs `hap` ys

hczipWith'' :: All c xs
            => Proxy c
            -> (forall a . c a => f a -> g a -> h a)
            -> NP f xs -> NP g xs -> NP h xs
hczipWith'' p f Nil       Nil       = Nil
hczipWith'' p f (x :* xs) (y :* ys) = f x y :* hczipWith'' p f xs ys

-- Defining heq via hczipWith''
heq' :: All Eq xs => NP I xs -> NP I xs -> Bool
heq' xs ys = and
           $ hcollapse
           $ hczipWith'' (Proxy :: Proxy Eq) (\x y -> K (x == y)) xs ys

-- Generalized heq
geq  :: (All Eq xs, All (Rep f) xs)
     => NP f xs -> NP f xs -> Bool
geq Nil       Nil       = True
geq (x :* xs) (y :* ys) = (to x) == (to y) && geq xs ys

-- General sequencing operation for NP
hsequence' :: (Applicative f)
           => NP (f :.: g) xs -> f (NP g xs)
hsequence' Nil            = pure Nil
-- (<$>) :: Functor     f =>   (a -> b) -> f a -> f b
-- (<*>) :: Applicative f => f (a -> b) -> f a -> f b
hsequence' (Comp x :* xs) = (:*) <$> x <*> hsequence' xs

-- Sequencing
hsequence  :: (Applicative f)
           => NP f xs -> f (NP I xs)
-- fmap I  :: Functor f => f a -> f (I a)
hsequence  =  hsequence' . hmap (Comp . fmap I)

-- Generalized foldr for NP
npfoldr :: (forall x . f x -> y -> y) -> y -> NP f xs -> y
npfoldr f x0 Nil       = x0
npfoldr f x0 (x :* xs) = f x (npfoldr f x0 xs)

-- hmap via npfoldr
--hmap' :: (forall x . f x -> g x) -> NP f xs -> NP g xs
--hmap' m xs = npfoldr (\x ys -> m x :* ys) Nil xs
