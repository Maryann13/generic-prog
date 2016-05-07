import Tests
import Generics.SOP (from)

-- Main program
main = do
    putStrLn $ show hlist  ++ " -- hlist"
    putStrLn $ show hklist ++ " -- hklist\n"
    putStrLn $ "expr:\n"   ++ show (from expr)  ++ "\n"
    putStrLn $ "expr1:\n"  ++ show (from expr1) ++ "\n"
    runTests
