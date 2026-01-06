module Main (main) where


import Ast
import Check
import Search


main :: IO ()
main = do
    let tA = PAtomic (Global "A")
    let tB = PAtomic (Global "B")
    let ptA = Plus tA (PShift (Not tA))
    putStrLn "CONSTRUCTIVE"
    putStrLn "1"
    let tyconstructive = (PShift (Or (NShift tA) (Not tA)))
    -- -- let tyy = (PShift (Or nA (Not (PShift nA))))
    let res3 = termSearch tyconstructive
    print res3
    putStrLn "2"
    let res4 = fmap (\r -> pCheck emptyCtx r tyconstructive) res3
    print res4
    putStrLn "CLASSICAL"
    let tyclassical = PShift (NShift ptA)
    -- let tyclassical = ptA
    putStrLn "3"
    let res5 = termSearch tyclassical
    print res5
    putStrLn "4"
    let res6 = fmap (\r -> pCheck emptyCtx r tyclassical) res5
    print res6
    putStrLn "IMPOSSIBLE"
    putStrLn "5"
    let res7 = termSearch ptA
    print res7
    print "Should be a function"
    let tyfancy = PShift (Or (Not tA) (NShift (Plus tA tB)))
    print tyfancy
    let res8 = termSearch tyfancy
    print res8
    let tyanother = PShift (Or (Not (Times tA tB)) (NShift (Plus tA tB)))
    print tyanother
    let res9 = termSearch tyfancy
    print res9
    let tyrelateors = PShift (Or (Not (Plus tA tB)) (Or (NShift tA) (NShift tB)))
    print tyrelateors
    let res10 = termSearch tyrelateors
    print res10

    -- let res3 = step $ Connect (PShift (Or (NShift tA) (Not tA))) Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)
    -- print res3
