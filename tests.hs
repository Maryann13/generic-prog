{-# LANGUAGE DataKinds, DeriveGeneric, FlexibleInstances, GADTs #-}
module Tests where

import GenericUniverse
import Exercises

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP (Generic)
import Control.Monad

-- ------------------------- Examples of lists
hlist  :: NP I '[Char, Bool, Int]
hlist  =  I 'x' :* I False :* I 3 :* Nil

hlist1 :: NP I '[Char, Bool, Int]
hlist1 =  I 'a' :* I False :* I 3 :* Nil

hlist2 :: NP I '[Char, Int]
hlist2 =  I 'b' :* I 13 :* Nil

hlist3 :: NP I '[Char, Int]
hlist3 =  I 'c' :* I 13 :* Nil

hlist4 :: NP I '[Char, Int]
hlist4 =  I 'b' :* I 7 :* Nil

hklist :: NP (K Int) '[Char, Bool, Int]
hklist =  K 13 :* K 24 :* K 5 :* Nil

-- ------------------------- Example of a datatype
-- An expression
data Expr = NumL Int | BoolL Bool | Add Expr Expr | If Expr Expr Expr
    deriving (GHC.Generic)

instance SOP.Generic Expr

--instance Iso f a => SOP.Generic (f a)

instance Show Expr where
    show (NumL   x) = show x
    show (BoolL  x) = show x
    show (Add  x y) = show x ++ " + " ++ show y
    show (If c x y) = "if " ++ show c ++ " then "
                            ++ show x ++
                      " else "
                            ++ show y

-- An example value of type Expr
expr :: Expr
expr  = If (BoolL True)
           (Add (NumL 13) (If (BoolL False)
                              (NumL 5)
                              (NumL 29)))
           (NumL 666)

expr1 :: Expr
expr1  = Add (NumL 19) (If (BoolL False)
                           (NumL 7)
                           (Add (NumL 14) (NumL 12)))

enum :: GEnum
enum  = Item2

enum1 :: GEnum
enum1  = Item3

-- ------------------------- Examples of NSs
type NSum f = NS (NP f) ('[ '[Bool, Char, Char],
                            '[Bool, Int],
                            '[Int]
                          ])
nsum1  :: NSum I
nsum1   = Z (I True :* I 'p' :* I 'q' :* Nil)
nsum1' :: NSum I
nsum1'  = Z (I True :* I 'q' :* I 'p' :* Nil)
nsum2  :: NSum I
nsum2   = S (Z (I False :* I 13 :* Nil))
nsum3  :: NSum I
nsum3   = S (S (Z (I 24 :* Nil)))

nsum4  :: ExampleNS
nsum4   = S (S (Z hlist2))
nsum5  :: ExampleNS
nsum5   = S (S (Z hlist3))
nsum6  :: ExampleNS
nsum6   = S (S (Z hlist4))

-- -------------------------

instance Eq a => Geq (NP (K a) xs) where
    (~=) Nil       Nil       = True
    (~=) (x :* xs) (y :* ys) = unK x == unK y && xs ~= ys

instance Geq (NP I '[]) where
    (~=) Nil       Nil       = True

-- ------------------------- Testing
assert :: Bool -> String -> IO ()
          -- if c then return () else error s
assert c s = unless c $ error s

runTests :: IO ()
runTests = do
    -- ------------------------- Lecture 1: Tests
    assert (      heq   hlist hlist)  "heq:   hlist == hlist"
    assert (not $ heq   hlist hlist1) "heq:   hlist == hlist1"
    assert (      heq'  hlist hlist)  "heq':  hlist == hlist"
    assert (not $ heq'  hlist hlist1) "heq':  hlist == hlist1"
    assert (      geqNP hlist hlist)  "geqNP: hlist == hlist"
    assert (not $ geqNP hlist hlist1) "geqNP: hlist == hlist1"
    assert (hlist == hlist)           "heq:   hlist == hlist"
    assert (hlist /= hlist1)          "heq:   hlist == hlist1"
    assert (hczipWith   pOrd (\x y -> K (x <= y)) hlist hlist1 ~= zlist)
           "hczipWith"
    assert (hczipWith'  pOrd (\x y -> K (x <= y)) hlist hlist1 ~= zlist)
           "hczipWith'"
    assert (hczipWith'' pOrd (\x y -> K (x <= y)) hlist hlist1 ~= zlist)
           "hczipWith''"
    assert (npfoldr (\_ n -> n + 1) 0 hlist == 3) "npfoldr"

    -- ------------------------- Lecture 2: Tests
    assert (compNP hlist hlist1 == GT) "compNP:  hlist  >  hlist1"
    assert (hlist  > hlist1)           "compare: hlist  >  hlist1"
    assert (compNP hlist hlist  == EQ) "compNP:  hlist  == hlist"
    assert (hlist1 <  hlist)           "compare: hlist1 <  hlist"
    assert (hlist1 <= hlist)           "compare: hlist1 <= hlist"
    assert (hlist  <= hlist)           "compare: hlist  <= hlist"

    assert (      skipGeqNP  hlist hlist1 mask1)  "skipGeqNP:  test 1"
    assert (not $ skipGeqNP  hlist hlist1 mask2)  "skipGeqNP:  test 2"
    assert (skipCompNP hlist hlist1 mask1 == EQ)  "skipCompNP: test 1"
    assert (skipCompNP hlist hlist1 mask2 == GT)  "skipCompNP: test 2"
    assert (skipCompNP hlist1 hlist mask2 == LT)  "skipCompNP: test 3"
    assert (compNP_N   hlist hlist1 two   == GT)  "compNP_N:   test 1"
    assert (compNP_N   hlist1 hlist one   == LT)  "compNP_N:   test 2"

    assert (nsum1 == nsum1) "nsum1 == nsum1"
    assert (nsum3 == nsum3) "nsum3 == nsum3"
    assert (nsum2 /= nsum3) "nsum2 /= nsum3"
    assert (nsum2  < nsum3) "nsum2  < nsum3"
    assert (nsum1 <= nsum2) "nsum1 <= nsum2"
    assert (nsum3 >= nsum1) "nsum3 >= nsum1"
    assert (nsum1' > nsum1) "nsum1' > nsum1"

    assert (skipCompNS nsum1 nsum2  nsMask1 == LT)  "skipCompNP: test 1"
    assert (skipCompNS nsum1 nsum1' nsMask1 == LT)  "skipCompNP: test 2"
    assert (skipCompNS nsum1 nsum1' nsMask2 == EQ)  "skipCompNP: test 3"
    assert (skipCompNS nsum2 nsum2  nsMask3 == EQ)  "skipCompNP: test 4"
    assert (compNS_N   nsum1 nsum1' two     == LT)  "compNS_N:   test 1"
    assert (compNS_N   nsum1 nsum1' one     == EQ)  "compNS_N:   test 2"

    assert exampleGeqNS' "exampleGeqNS'"

    assert (hlist2 ~=  hlist3) "hlist2 ~=  hlist3"
    assert (hlist2 ~/= hlist4) "hlist2 ~/= hlist4"

    assert (geqNS' nsum4 nsum5) "nsum4 ~=  nsum5"
    assert (nsum4 ~/= nsum6)    "nsum4 ~/= nsum6"

    assert (SOP nsum1 == SOP nsum1) "SOP nsum1 == SOP nsum1"
    assert (SOP nsum4 ~= SOP nsum5) "SOP nsum4 ~= SOP nsum5"

    assert (      geq (I enum) (I enum )) "geq"
    assert (not $ geq (I enum) (I enum1)) "geq"

    assert (      ggeq (I enum) (I enum )) "ggeq"
    assert (not $ ggeq (I enum) (I enum1)) "ggeq"

    assert (comp (I enum ) (I enum ) == EQ) "comp"
    assert (comp (I enum ) (I enum1) == LT) "comp"
    assert (comp (I enum1) (I enum ) == GT) "comp"

    putStrLn "Testing: OK, passed all tests."
        where
              pOrd    = Proxy :: Proxy Ord
              zlist   = K False :* K True :* K True :* Nil
              mask1   = zlist
              mask2   = K True :* K False :* K False :* Nil
              one     = Suc Zero
              two     = Suc one
              nsMask1 = Z mask1
              nsMask2 = Z mask2
              nsMask3 = S (Z (K False :* K True :* Nil))
