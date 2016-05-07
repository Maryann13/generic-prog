{-# LANGUAGE ConstraintKinds, TypeOperators, TypeFamilies,
    RankNTypes, FlexibleInstances, DataKinds, UndecidableInstances,
    AllowAmbiguousTypes, MultiParamTypeClasses                      #-}
module Exercises where

import GenericUniverse
import Instances ()

-- Mapping of 2nd order with a constrained function
hcmap_2 :: All c xs
        => Proxy c
        -> (forall x . c x => f x -> g x -> h x)
        -> NP f xs -> NP (g -.-> h) xs
hcmap_2 _ _ Nil       = Nil
hcmap_2 p m (x :* xs) = Fn (m x) :* hcmap_2 p m xs

-- ------------------------------------------- Lecture 1: Exercises
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
hczipWith'' _ _ Nil       Nil       = Nil
hczipWith'' p f (x :* xs) (y :* ys) = f x y :* hczipWith'' p f xs ys

-- Defining heq via hczipWith''
heq' :: All Eq xs => NP I xs -> NP I xs -> Bool
heq' xs ys = and
           $ hcollapse
           $ hczipWith'' (Proxy :: Proxy Eq) (\x y -> K (x == y)) xs ys

-- Generalized heq
geqNP :: (All Eq xs, All (Iso f) xs)
      => NP f xs -> NP f xs -> Bool
geqNP Nil       Nil       = True
geqNP (x :* xs) (y :* ys) = from x == from y && geqNP xs ys

instance (All Eq xs, All (Iso f) xs) => Eq (NP f xs) where
    (==) = geqNP

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
npfoldr _ x0 Nil       = x0
npfoldr f x0 (x :* xs) = f x (npfoldr f x0 xs)

-- hmap via npfoldr
--hmap' :: (forall x . f x -> g x) -> NP f xs -> NP g xs
--hmap' m xs = npfoldr (\x ys -> m x :* ys) Nil xs

ones = hcpure (Proxy :: Proxy Num) (I 1) :: NP I '[Int, Int]

-- ------------------------------------------- Lecture 2: Exercises
-- Comparison for NP
compNP :: (All Ord xs, All (Iso f) xs)
       => NP f xs -> NP f xs -> Ordering
compNP Nil       Nil       = EQ
compNP (x :* xs) (y :* ys) = case compare (from x) (from y) of
                                  EQ -> compNP xs ys
                                  LT -> LT
                                  GT -> GT

instance (All Eq xs, All Ord xs, All (Iso f) xs) => Ord (NP f xs) where
    compare = compNP

{- A list of bools to indicate for each x in a list of
   constructor arguments if it must be considered      -}
type Mask xs = NP (K Bool) xs

{- A variant of generic equality for NP
   skipping some constructor arguments  -}
skipGeqNP :: (All Eq xs, All (Iso f) xs)
          => NP f xs -> NP f xs -> Mask xs -> Bool
skipGeqNP Nil       Nil       Nil       = True
skipGeqNP (x :* xs) (y :* ys) (s :* ss)
    | unK s     = from x == from y && skipGeqNP xs ys ss
    | otherwise = skipGeqNP xs ys ss

{- A variant of generic comparison for NP
   skipping some constructor arguments    -}
skipCompNP :: (All Ord xs, All (Iso f) xs)
           => NP f xs -> NP f xs -> Mask xs -> Ordering
skipCompNP Nil       Nil       Nil       = EQ
skipCompNP (x :* xs) (y :* ys) (s :* ss)
    | unK s     = case compare (from x) (from y) of
                       EQ -> skipCompNP xs ys ss
                       LT -> LT
                       GT -> GT
    | otherwise = skipCompNP xs ys ss

{- A variant of generic comparison for NP
  that compares first N constructor arguments -}
compNP_N :: (All Ord xs, All (Iso f) xs)
         => NP f xs -> NP f xs -> Nat -> Ordering
compNP_N _         _         Zero    = EQ
compNP_N Nil       Nil       (Suc _) = error "compNP_N: N out of range"
compNP_N (x :* xs) (y :* ys) (Suc n) = case compare (from x) (from y) of
                                            EQ -> compNP_N xs ys n
                                            LT -> LT
                                            GT -> GT

-- Equality for NS of NPs
geqNS :: (All2 Eq xss, All2 (Iso f) xss)
      => NS (NP f) xss -> NS (NP f) xss -> Bool
geqNS (Z np1) (Z np2) = geqNP np1 np2
geqNS (S ns1) (S ns2) = geqNS ns1 ns2
geqNS _       _       = False

instance (All2 Eq xss, All2 (Iso f) xss) => Eq (NS (NP f) xss) where
    (==) = geqNS

instance (All2 Eq xss, All2 Ord xss, All2 (Iso f) xss)
        => Ord (NS (NP f) xss) where
    compare = compNS

-- Comparison for NS of NPs
compNS :: (All2 Ord xss, All2 (Iso f) xss)
       => NS (NP f) xss -> NS (NP f) xss -> Ordering
compNS (Z np1) (Z np2) = compNP np1 np2
compNS (S ns1) (S ns2) = compNS ns1 ns2
compNS (S _)   (Z _)   = GT
compNS (Z _)   (S _)   = LT

{- A variant of generic comparison for NS of NPs
   skipping some constructor arguments           -}
skipCompNS :: (All2 Ord xss, All2 (Iso f) xss)
           => NS (NP f) xss -> NS (NP f) xss -> NS (NP (K Bool)) xss
           -> Ordering
skipCompNS (Z np1) (Z np2) (Z nps) = skipCompNP np1 np2 nps
skipCompNS (S ns1) (S ns2) (S nss) = skipCompNS ns1 ns2 nss
skipCompNS (S _)   (S _)   (Z _)   = error "skipCompNS: arguments out of range"
skipCompNS (Z _)   (Z _)   (S _)   = error "skipCompNS: arguments out of range"
skipCompNS (S _)   (Z _)   _       = GT
skipCompNS (Z _)   (S _)   _       = LT

{- A variant of generic comparison for NS of NPs
   that compares first N constructor arguments   -}
compNS_N :: (All2 Ord xss, All2 (Iso f) xss)
         => NS (NP f) xss -> NS (NP f) xss -> Nat -> Ordering
compNS_N (Z np1) (Z np2) n = compNP_N np1 np2 n
compNS_N (S ns1) (S ns2) n = compNS_N ns1 ns2 n
compNS_N (S _)   (Z _)   _ = GT
compNS_N (Z _)   (S _)   _ = LT

type ExampleNS = NS (NP I) ('[ '[Bool, Char],
                               '[Int, Bool, Int],
                               '[Char, Int]
                             ])
exampleNS1 :: ExampleNS
exampleNS1  = S (Z (I 13 :* I False :* I 42 :* Nil))
exampleNS2 :: ExampleNS
exampleNS2  = S (Z (I 13 :* I True  :* I 42 :* Nil))

exampleGeqNS :: ExampleNS -> ExampleNS -> Bool
exampleGeqNS (Z (I x1 :* _))
             (Z (I y1 :* _))
    = x1 == y1
exampleGeqNS (S (Z (I x1 :* _ :* I x3 :* Nil)))
             (S (Z (I y1 :* _ :* I y3 :* Nil)))
    = x1 == y1 && x3 == y3
exampleGeqNS (S (S (Z (_ :* I x2 :* Nil))))
             (S (S (Z (_ :* I y2 :* Nil))))
    = x2 == y2
exampleGeqNS _ _ = False

exampleGeqNS' = exampleGeqNS exampleNS1 exampleNS2 -- True

-- The class defines generic equality
class Geq a where
    (~=), (~/=)  :: a -> a -> Bool
    (~/=) x y     = not (x ~= y)

instance Geq (NP I '[Bool, Char]) where
    (~=) (I x1 :* _) (I y1 :* _) = x1 == y1
instance Geq (NP I '[Int, Bool, Int]) where
    (~=) (I x1 :* _ :* I x3 :* Nil) (I y1 :* _ :* I y3 :* Nil)
        = x1 == y1 && x3 == y3
instance Geq (NP I '[Char, Int]) where
    (~=) (_ :* I x2 :* Nil) (_ :* I y2 :* Nil) = x2 == y2

{- A variant of generic equality for NS of NPs
   requiring a Geq constraint for all NPs      -}
geqNS' :: (All_NP Geq f xss)
       => NS (NP f) xss -> NS (NP f) xss -> Bool
geqNS' (Z np1) (Z np2) = np1 ~= np2
geqNS' (S ns1) (S ns2) = geqNS' ns1 ns2
geqNS' _       _       = False

instance (All_NP Geq f xss) => Geq (NS (NP f) xss) where
   (~=) = geqNS'

-- Equality for SOP
geqSOP :: (All2 Eq xss, All2 (Iso f) xss)
       => SOP f xss -> SOP f xss -> Bool
geqSOP (SOP sop1) (SOP sop2) = geqNS sop1 sop2

-- Generic equality for SOP
geqSOP' :: (All_NP Geq f xss)
        => SOP f xss -> SOP f xss -> Bool
geqSOP' (SOP sop1) (SOP sop2) = geqNS' sop1 sop2

instance (All2 Eq xss, All2 (Iso f) xss) => Eq (SOP f xss) where
    (==) = geqSOP

instance (All_NP Geq f xss) => Geq (SOP f xss) where
    (~=) = geqSOP'

-- Comparison for SOP
compSOP :: (All2 Ord xss, All2 (Iso f) xss)
        => SOP f xss -> SOP f xss -> Ordering
compSOP (SOP sop1) (SOP sop2) = compNS sop1 sop2

-- Equality for all representable types
geq :: (Generic f a, All2 Eq (Code a), All2 (Iso f) (Code a))
    => f a -> f a -> Bool
geq x y = geqSOP (gfrom x) (gfrom y)

-- Generic equality for all representable types
ggeq :: (Generic f a, All_NP Geq f (Code a))
     => f a -> f a -> Bool
ggeq x y = geqSOP' (gfrom x) (gfrom y)

-- Comparison for all representable types
comp :: (Generic f a, All2 Ord (Code a), All2 (Iso f) (Code a))
     => f a -> f a -> Ordering
comp x y = compSOP (gfrom x) (gfrom y)

-- Generic enumeration: declaration
data GEnum = Item1 | Item2 | Item3 | Item4 | Item5

fromGEnum :: GEnum -> NS (NP I) (Code GEnum)
fromGEnum Item1 = Z Nil
fromGEnum Item2 = S (Z Nil)
fromGEnum Item3 = S (S (Z Nil))
fromGEnum Item4 = S (S (S (Z Nil)))
fromGEnum Item5 = S (S (S (S (Z Nil))))

toGEnum :: NS (NP I) (Code GEnum) -> GEnum
toGEnum (Z Nil)                 = Item1
toGEnum (S (Z Nil))             = Item2
toGEnum (S (S (Z Nil)))         = Item3
toGEnum (S (S (S (Z Nil))))     = Item4
toGEnum (S (S (S (S (Z Nil))))) = Item5

-- Generic enumeration: definition
instance Generic I GEnum where
    type Code GEnum = '[ '[],
                         '[],
                         '[],
                         '[],
                         '[]
                       ]
    gfrom (I x) = SOP (fromGEnum x)
    gto (SOP x) = I   (toGEnum   x)
