{-# LANGUAGE CPP, UndecidableInstances, RankNTypes, DataKinds, TypeOperators,
    DefaultSignatures, KindSignatures, TypeFamilies, ConstraintKinds,
    FlexibleContexts, FlexibleInstances, AllowAmbiguousTypes                  #-}
module SOPGeneric where

import Data.Proxy
import qualified GHC.Generics as GHC (Generic, Rep)
import GHC.Generics as GHC hiding (Generic, Rep)
import Generics.SOP.BasicFunctors as SOP
import Generics.SOP.Constraint as SOP
import Generics.SOP.NP as SOP
import Generics.SOP.NS as SOP
import Generics.SOP.Sing

-- The (generic) representation of a datatype
type Rep a = SOP I (Code a)

-- The class of representable datatypes
class (All SListI (Code a)) => Generic (a :: *) where
  type Code a :: [[*]]
  type Code a = GCode a

  -- Converts from a value to its structural representation
  from         :: a -> Rep a
  default from :: (GFrom a, GHC.Generic a) => a -> SOP I (GCode a)
  from = gfrom

  -- Converts from a structural representation back to the
  -- original value
  to         :: Rep a -> a
  default to :: (GTo a, GHC.Generic a) => SOP I (GCode a) -> a
  to = gto

-- -----------------------------------------
type GCode (a :: *) = ToSumCode (GHC.Rep a) '[]

-- Constraint for the class that computes 'gfrom'
type GFrom a = GSumFrom (GHC.Rep a)

-- Constraint for the class that computes 'gto'
type GTo a = GSumTo (GHC.Rep a)

class GSingleFrom (a :: * -> *) where
  gSingleFrom :: a x -> ToSingleCode a

class GSingleTo (a :: * -> *) where
  gSingleTo :: ToSingleCode a -> a x

class GProductFrom (a :: * -> *) where
  gProductFrom :: a x -> NP I xs -> NP I (ToProductCode a xs)

class GProductTo (a :: * -> *) where
  gProductTo :: NP I (ToProductCode a xs) -> (a x -> NP I xs -> r) -> r

class GSumFrom (a :: * -> *) where
  gSumFrom :: a x -> SOP I xss -> SOP I (ToSumCode a xss)
  gSumSkip :: proxy a -> SOP I xss -> SOP I (ToSumCode a xss)

class GSumTo (a :: * -> *) where
  gSumTo :: SOP I (ToSumCode a xss) -> (a x -> r) -> (SOP I xss -> r) -> r

type family ToSingleCode (a :: * -> *) :: *

type family ToSumCode (a :: * -> *) (xs :: [[*]]) :: [[*]]

type family ToProductCode (a :: * -> *) (xs :: [*]) :: [*]

-- An automatically computed version of 'SOPGenerics.from'
gfrom :: (GFrom a, GHC.Generic a) => a -> SOP I (GCode a)
gfrom x = gSumFrom (GHC.from x) (error "gfrom: internal error" :: SOP.SOP SOP.I '[])

-- An automatically computed version of 'SOPGenerics.to'
gto :: forall a. (GTo a, GHC.Generic a) => SOP I (GCode a) -> a
gto x = GHC.to (gSumTo x id ((\ _ -> error "inaccessible") :: SOP I '[] -> (GHC.Rep a) x))

-- ----------------------------------------- Instances
-- ----------------------- GSingleFrom instance
instance GSingleFrom (K1 i a) where
  gSingleFrom (K1 a) = a

-- ----------------------- GSingleTo instance
instance GSingleTo (K1 i a) where
  gSingleTo a = K1 a

-- ----------------------- GProductFrom instances
instance (GProductFrom a, GProductFrom b) => GProductFrom (a :*: b) where
  gProductFrom (a :*: b) xs = gProductFrom a (gProductFrom b xs)

instance GProductFrom U1 where
  gProductFrom U1 xs = xs

instance GSingleFrom a => GProductFrom (M1 S c a) where
  gProductFrom (M1 a) xs = I (gSingleFrom a) :* xs

-- ----------------------- GProductTo instances
instance (GProductTo a, GProductTo b) => GProductTo (a :*: b) where
  gProductTo xs k = gProductTo xs (\ a ys -> gProductTo ys (\ b zs -> k (a :*: b) zs))

instance GSingleTo a => GProductTo (M1 S c a) where
  gProductTo (SOP.I a :* xs) k = k (M1 (gSingleTo a)) xs
#if __GLASGOW_HASKELL__ < 800
  gProductTo _               _ = error "inaccessible"
#endif

instance GProductTo U1 where
  gProductTo xs k = k U1 xs

-- ----------------------- GSumFrom instances
instance (GSumFrom a, GSumFrom b) => GSumFrom (a :+: b) where
  gSumFrom (L1 a) xss = gSumFrom a (gSumSkip (Proxy :: Proxy b) xss)
  gSumFrom (R1 b) xss = gSumSkip (Proxy :: Proxy a) (gSumFrom b xss)

  gSumSkip _ xss = gSumSkip (Proxy :: Proxy a) (gSumSkip (Proxy :: Proxy b) xss)

instance (GSumFrom a) => GSumFrom (M1 D c a) where
  gSumFrom (M1 a) xss = gSumFrom a xss
  gSumSkip _      xss = gSumSkip (Proxy :: Proxy a) xss

instance (GProductFrom a) => GSumFrom (M1 C c a) where
  gSumFrom (M1 a) _    = SOP (Z (gProductFrom a Nil))
  gSumSkip _ (SOP xss) = SOP (S xss)

-- ----------------------- GSumTo instances
instance (GSumTo a, GSumTo b) => GSumTo (a :+: b) where
  gSumTo xss s k = gSumTo xss (s . L1) (\ r -> gSumTo r (s . R1) k)

instance (GProductTo a) => GSumTo (M1 C c a) where
  gSumTo (SOP (Z xs)) s _ = s (M1 (gProductTo xs ((\ x Nil -> x) :: a x -> NP I '[] -> a x)))
  gSumTo (SOP (S xs)) _ k = k (SOP xs)

instance (GSumTo a) => GSumTo (M1 D c a) where
  gSumTo xss s k = gSumTo xss (s . M1)

-- ----------------------- Type instances
type instance ToSingleCode (K1 _i a) = a

type instance ToProductCode (a :*: b)   xs = ToProductCode a (ToProductCode b xs)
type instance ToProductCode U1          xs = xs
type instance ToProductCode (M1 S _c a) xs = ToSingleCode a ': xs

type instance ToSumCode (a :+: b)   xs = ToSumCode a (ToSumCode b xs)
type instance ToSumCode V1          xs = xs
type instance ToSumCode (M1 D _c a) xs = ToSumCode a xs
type instance ToSumCode (M1 C _c a) xs = ToProductCode a '[] ': xs
