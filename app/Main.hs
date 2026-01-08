module Main (main) where

import Ast
import Check
import Search

checkSearch :: PType -> IO ()
checkSearch ty = do
    print ty
    let res = termSearch ty
    print res
    let res2 = fmap (\r -> pCheck emptyCtx r ty) res
    print res2
    putStrLn ""

main :: IO ()
main = do
    let tA = PAtomic (Global "A")
    let tB = PAtomic (Global "B")
    let lemA = Plus tA (PShift (Not tA))
    putStrLn "CONSTRUCTIVE LEM"
    let tyconstructive = (PShift (Or (NShift tA) (Not tA)))
    checkSearch tyconstructive
    -- -- let tyy = (PShift (Or nA (Not (PShift nA))))
    -- let res3 = termSearch tyconstructive
    -- print res3
    -- putStrLn "2"
    -- let res4 = fmap (\r -> pCheck emptyCtx r tyconstructive) res3
    -- print res4
    putStrLn "CLASSICAL LEM"
    let tyclassical = PShift (NShift lemA)
    checkSearch tyclassical
    -- let tyclassical = ptA
    -- putStrLn "3"
    -- let res5 = termSearch tyclassical
    -- print res5
    -- putStrLn "4"
    -- let res6 = fmap (\r -> pCheck emptyCtx r tyclassical) res5
    -- print res6
    putStrLn "IMPOSSIBLE"
    checkSearch lemA
    putStrLn "SHOULD BE FUNCTIONS:"
    putStrLn "A -> A + B"
    let tyfancy = PShift (Or (Not tA) (NShift (Plus tA tB)))
    checkSearch tyfancy
    putStrLn "A x B -> A + B"
    let tyanother = PShift (Or (Not (Times tA tB)) (NShift (Plus tA tB)))
    checkSearch tyanother
    putStrLn "A + B -> A par B"
    let tyrelateors = PShift (Or (Not (Plus tA tB)) (Or (NShift tA) (NShift tB)))
    checkSearch tyrelateors
    putStrLn "A -> (-)(~A)"
    let tydni = PShift (Or (NShift (Minus (Not tA))) (Not tA))
    checkSearch tydni
    putStrLn "(-)(~A) -> A"
    let tydne = PShift (Or (Not (Minus (Not tA))) (NShift tA))
    checkSearch tydne
    let tydne2 = PShift (Or (Not (PShift (Not (PShift (Not tA))))) (NShift tA))
    checkSearch tydne2
    let tywhatever = Plus (Times tydni tydne) lemA
    checkSearch tywhatever
    let tywhatever2 = Plus lemA (Times (Plus (Times tydni tyrelateors) lemA) tydne)
    checkSearch tywhatever2
    -- let res3 = step $ Connect (PShift (Or (NShift tA) (Not tA))) Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)
    -- print res3
