module Main (main) where

import Ast
import Check
import Search
import Text.Parsec
import Parse (parseLine)

checkSearch :: (Show a, Show b) => (a -> Either Errors b) -> (Context -> b -> a -> Either Errors ()) -> a -> IO ()
checkSearch search check ty = do
    print ty
    let res = search ty
    case res of
        Left errs -> do
            putStrLn "Failed to find term for type:"
            putStr "\t"
            print errs
        Right tm -> do
            putStrLn "Found term:"
            putStr "\t"
            print tm
    let res2 = res >>= (\r -> check emptyCtx r ty)
    case res2 of
        Left errs -> do
            putStrLn "Search result failed to typecheck:"
            putStr "\t"
            print errs
        Right () -> putStrLn "Typechecks!"
    putStrLn ""



main :: IO ()
main = do
    putStrLn "Enter a polarized type:"
    text <- getLine
    case (parse parseLine "" text) of
        Right (Positive ty) -> checkSearch termSearch pCheck ty
        Right (Negative ty) -> checkSearch cotermSearch nCheck ty
        Left errs -> do
            putStrLn "Failed to parse:"
            putStr "\t"
            print errs

    if text == "QUIT" then return () else main
    -- let tA = PAtomic (Global "A")
    -- let tB = PAtomic (Global "B")
    -- let lemA = Plus tA (PShift (Not tA))
    -- putStrLn "CONSTRUCTIVE LEM"
    -- let tyconstructive = (PShift (Or (NShift tA) (Not tA)))
    -- checkSearch tyconstructive
    -- putStrLn "CLASSICAL LEM"
    -- let tyclassical = PShift (NShift lemA)
    -- checkSearch tyclassical
    -- putStrLn "IMPOSSIBLE (expect failure)"
    -- checkSearch lemA
    -- putStrLn "SHOULD BE FUNCTIONS:"
    -- putStrLn "A -> A + B"
    -- let tyfancy = PShift (Or (Not tA) (NShift (Plus tA tB)))
    -- checkSearch tyfancy
    -- putStrLn "A x B -> A + B"
    -- let tyanother = PShift (Or (Not (Times tA tB)) (NShift (Plus tA tB)))
    -- checkSearch tyanother
    -- putStrLn "A + B -> A par B"
    -- let tyrelateors = PShift (Or (Not (Plus tA tB)) (Or (NShift tA) (NShift tB)))
    -- checkSearch tyrelateors
    -- putStrLn "A -> (-)(~A)"
    -- let tydni = PShift (Or (NShift (Minus (Not tA))) (Not tA))
    -- checkSearch tydni
    -- putStrLn "(-)(~A) -> A"
    -- let tydne = PShift (Or (Not (Minus (Not tA))) (NShift tA))
    -- checkSearch tydne
    -- let tydne2 = PShift (Or (Not (PShift (Not (PShift (Not tA))))) (NShift tA))
    -- checkSearch tydne2
    -- let tywhatever = Plus (Times tydni tydne) lemA
    -- checkSearch tywhatever
    -- let tywhatever2 = Plus lemA (Times (Plus (Times tydni tyrelateors) lemA) tydne)
    -- checkSearch tywhatever2
    -- let res3 = step $ Connect (PShift (Or (NShift tA) (Not tA))) Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)
    -- print res3
