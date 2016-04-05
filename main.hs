{-# LANGUAGE DataKinds #-}
import GenericProg
import Exercises

-- ------------------------- Examples of lists
hlist  :: NP I '[Char, Bool, Int]
hlist  =  I 'x' :* I False :* I 3 :* Nil

hlist1 :: NP I '[Char, Bool, Int]
hlist1 =  I 'a' :* I False :* I 3 :* Nil

hklist :: NP (K Int) '[Char, Bool, Int]
hklist =  K 13 :* K 24 :* K 5 :* Nil

-- Main program
main = do
    putStrLn $ show hlist  ++ " -- hlist"
    putStrLn $ show hklist ++ " -- hklist\n"
    putStrLn   "heq:"
    putStrLn $ "hlist == hlist:  " ++ (show $ hlist `heq`  hlist)
    putStrLn $ "hlist == hlist1: " ++ (show $ hlist `heq`  hlist1)
    putStrLn   "\nheq':"
    putStrLn $ "hlist == hlist:  " ++ (show $ hlist `heq'` hlist)
    putStrLn $ "hlist == hlist1: " ++ (show $ hlist `heq'` hlist1)
    putStrLn   "\ngeq:"
    putStrLn $ "hlist == hlist:  " ++ (show $ hlist `geq`  hlist)
    putStrLn $ "hlist == hlist1: " ++ (show $ hlist `geq`  hlist1) ++ "\n"
    putStrLn $
        (show $ hczipWith   (Proxy :: Proxy Ord) (\x y -> K (x <= y)) hlist hlist1)
        ++ " -- hczipWith"
    putStrLn $
        (show $ hczipWith'  (Proxy :: Proxy Ord) (\x y -> K (x <= y)) hlist hlist1)
        ++ " -- hczipWith'"
    putStrLn $
        (show $ hczipWith'' (Proxy :: Proxy Ord) (\x y -> K (x <= y)) hlist hlist1)
        ++ " -- hczipWith''"
    putStrLn $ (show $ npfoldr (\_ n -> n + 1) 0  hlist) ++ " -- length via npfoldr"
