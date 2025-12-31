module Main (main) where

import Debug.Trace (trace)
import Data.Tuple (swap)
import Control.Applicative (Alternative(..))

import Ast
import Check
import Ast (SearchState)

justErr :: a -> Maybe b -> Either a b
justErr a Nothing = Left a
justErr _ (Just b) = Right b

findType :: Context -> Type -> Either Errors Name
findType (vars, _) (Positive ty) = justErr (mkErr ("No var of type " ++ show ty)) $ lookup ty $ map swap vars
findType (_, covars) (Negative ty) = justErr (mkErr ("No covar of type " ++ show ty)) $ lookup ty $ map swap covars

checkVar :: Context -> PType -> Either Errors Term
checkVar ctx ty = do
    n <- findType ctx (Positive ty)
    return $ Var n

checkCovar :: Context -> NType -> Either Errors Coterm
checkCovar ctx ty = do
    n <- findType ctx (Negative ty)
    return $ Covar n

checkContext :: Context -> Either Errors Command
checkContext ctx = trace "checking for matching pair in context" backtrack helper3 (maxSize ctx)
        -- return x
    where
        helper3 k = do
            x <- helper2 ctx k
            helper ctx x

        helper2 :: Context -> Int -> Either Errors Type
        helper2 ([], []) _ = Left $ mkErr $ "empty context has nothing to select"
        helper2 ((_, t):_, _) 0 = return $ Positive t
        helper2 ([], (_, t):_) 0 = return $ Negative t
        helper2 (_:xs, ys) k = helper2 (xs, ys) (k - 1)
        helper2 ([], _:ys) k = helper2 ([], ys) (k - 1)

        helper cx (Positive pt) = do
            tm <- checkVar cx pt
            co <- checkCovar cx (NShift pt)
            return $ Connect (Positive pt) tm co
        helper cx (Negative nt) = do
            tm <- checkVar cx (PShift nt)
            co <- checkCovar cx nt
            return $ Connect (Negative nt) tm co

mismatch :: SearchState -> Context -> Maybe (Name, Type)
mismatch _ ([], []) = Nothing
mismatch ii (x@(_, PShift _):xs, ys) = mismatch ii (xs, ys)
mismatch ii ((xs, y@(_, NShift _):ys)) = mismatch ii (xs, ys)
mismatch ii (x@(_, PAtomic _):xs, ys) = mismatch ii (xs, ys)
mismatch ii ((xs, y@(_, NAtomic _):ys)) = mismatch ii (xs, ys)
-- mismatch (x@(n, pt):xs, ys) = ((x:xs, ys), Just (n, Positive pt))
-- mismatch (xs, y@(n, nt):ys) = ((xs, y:ys), Just (n, Negative nt))
mismatch _ ((n, pt):_, _) = trace ("+type " ++ show pt ++ " is neither shift nor atomic") $ Just (n, Positive pt)
mismatch _ (_, (n, nt):_) = trace ("-type " ++ show nt ++ " is neither shift nor atomic") $ Just (n, Negative nt)
-- mismatch ii ((n, pt):xs, ys) = if seen n ii then mismatch ii (xs, ys) else trace ("+type " ++ show pt ++ " is neither shift nor atomic") $ Just (n, Positive pt)
-- mismatch ii (xs, (n, nt):ys) = if seen n ii then mismatch ii (xs, ys) else trace ("-type " ++ show nt ++ " is neither shift nor atomic") $ Just (n, Negative nt)
    
-- mismatch :: Context -> (Context, Maybe (Name, Type))
-- mismatch ([], []) = (([], []), Nothing)
-- mismatch ((n, PShift nt):xs, ys) = ((xs, ys), Just (n, Negative nt))
-- mismatch ((xs, (n, NShift pt):ys)) = ((xs, ys), Just (n, Positive pt))
-- mismatch (x:xs, ys) = case mismatch (xs, ys) of
--     ((xs', ys'), res) -> ((x:xs', ys'), res)
-- mismatch (xs, y:ys) = case mismatch (xs, ys) of
--     ((xs', ys'), res) -> ((xs', y:ys'), res)

focus :: Int -> Context -> Either Errors (Name, Type)
focus k ([], []) = trace "empty" $ Left $ mkErr $ "Cannot focus in empty context" ++ show k
focus 0 ((n, PShift ty):xs, ys) = trace ("got negative " ++ show n) Right (n, Negative ty)
focus 0 (xs, (n, NShift ty):ys) = trace ("got positive " ++ show n) Right (n, Positive ty)
focus 0 ctx = Left $ mkErr $ "OH NOOOOOO Non-shifted in context " ++ showCtx ctx ++ " (should be impossible)"
focus k (x:xs, ys) = trace ("countingleft:" ++ show k) focus (k - 1) (xs, ys)
focus k ([], y:ys) = trace ("countingright:" ++ show k) $ focus (k - 1) ([], ys)
-- focus k (xs, ys)

focuser :: SearchState -> Int -> Context -> Either Errors Command
focuser _ 0 ctx = Left $ mkErr $ "Focused through whole context " ++ showCtx ctx ++ "and got nothing"
focuser ii k ctx = trace ("focusing formula " ++ show k ++ " of " ++ show (maxSize ctx) ++ " " ++ showCtx ctx) $ (do
    pair <- focus (k - 1) ctx
    let (name, ty) = pair
    _ <- if seen name ii then trace "seenf" Left (mkErr ("Already seen " ++ show name)) else return ()
    let ii' = trace ("noting " ++ show name) note name ii
    case ty of
        Positive pt -> trace ("focusing positive " ++ show name ++ ": " ++ show pt ++ "\n\t" ++ showCtx ctx) $ do
            tm <- pFocusSearch ii' ctx pt
            return $ Connect (Positive pt) tm (Covar name)
        Negative nt -> trace ("focusing negative " ++ show name ++ ": " ++ show nt ++ "\n\t" ++ showCtx ctx) $ do
            co <-  nFocusSearch ii' ctx nt
            return $ Connect (Negative nt) (Var name) co
    ) <|> focuser ii (k - 1) ctx

maxSize :: Context -> Int
maxSize (xs, ys) = length xs + length ys

-- nonFocuser k = 

backtrack :: Alternative f => (Int -> f a) -> Int -> f a
backtrack f 0 = f 0
backtrack f k = f k <|> backtrack f (k - 1)

-- we need backtracking explicitly here
blurSearch :: SearchState -> Context -> Either Errors Command
-- blurSearch ii ctx = trace ("making a command of type " ++ showCtx ctx) $ 
blurSearch ii ctx = trace ("making a command of type\n\t" ++ showCtx ctx) $ checkContext ctx <|> let res = mismatch ii ctx in trace ("mismatch: " ++ show res ++ "\n\t" ++ showCtx ctx) $ case res of
    Nothing -> trace ("focusing in context\n\t" ++ showCtx ctx) $ focuser ii (maxSize ctx) ctx
    -- Just (name, ty) ->
    Just (name, ty) -> case ty of
        Positive pt -> do
            -- cmd <- trace ("getting positive blur " ++ show name ++ ": " ++ show pt) $ blurSearch ii ctx'
            co <- trace ("getting nBlur " ++ show name ++ ": " ++ show pt ++ " at\n\t" ++ showCtx ctx) $ nBlur ii ctx pt
            -- nCheck ctx' co (NShift pt)
            return $ trace ("muing positive mismatch " ++ show name) $ Connect (Positive pt) (Var name) co
        Negative nt -> do
            -- cmd <- trace ("getting negative blur" ++ show name ++ ": " ++ show nt) $ blurSearch ii ctx' 
            tm <- trace ("getting pBlur " ++ show name ++ ": " ++ show nt) $ pBlur ii ctx nt
            -- pCheck ctx' tm (PShift nt)
            return $ trace "muing negative mismatch" $ Connect (Negative nt) tm (Covar name)
            -- return $ Connect (Negative nt) (Mu name cmd) (Covar name)
-- blurSearch ii ([], []) = Nothing
-- blurSearch ii ((n, PShift nt):xs, ys) = fmap (\v -> Connect (Negative nt) v (Covar n)) (pBlur ii (xs, ys) nt) -- is this right
-- blurSearch ii (xs, (n, NShift pt):ys) = fmap (Connect (Positive pt) (Var n)) (nBlur ii (xs, ys) pt)
-- blurSearch ii (x:xs, y:ys) = blurSearch ii ()

pBlur :: SearchState -> Context -> NType -> Either Errors Term
pBlur _ _ Bot = Left $ mkErr "Cannot prove Bot"
pBlur _ ctx t@(NAtomic _) = trace "chVar" checkVar ctx (PShift t) -- fmap (Mu (Local ii)) $ blurSearch (ii + 1) $ nBind (Local ii) t ctx
pBlur ii ctx (And a b) = let (ii', name) = getName ii in do
    c1 <- blurSearch ii' (nBind name a ctx)
    c2 <- blurSearch ii' (nBind name b ctx)
    return $ MuAnd (name, c1) (name, c2)
pBlur ii ctx (Or a b) = let (ii', name1) = getName ii in
    let (ii'', name2) = getName ii' in
    trace "orrr" $ fmap (MuOr (name1, name2)) $ blurSearch ii'' (nBind name1 a (nBind name2 b ctx))
pBlur ii ctx (Not p) = let (ii', name) = getName ii in
    trace "nottt" $ fmap (MuNot name) $ blurSearch ii' (pBind name p ctx)
pBlur ii ctx (NShift p) = let (ii', name) = getName ii in
    trace "double-shifted! mooing" $ fmap (Mu name) $ blurSearch ii' (nBind name (NShift p) ctx)
-- pBlur ctx 

nBlur :: SearchState -> Context -> PType -> Either Errors Coterm
nBlur _ _ Top = Left $ mkErr "Cannot disprove Top"
nBlur _ ctx t@(PAtomic _) = trace ("checking for covar of type " ++ show t ++ " in ctx\n\t" ++ showCtx ctx) checkCovar ctx (NShift t)
nBlur ii ctx (Times a b) = let (ii', name1) = getName ii in
    let (ii'', name2) = getName ii' in
    fmap (MatchTimes (name1, name2)) $ blurSearch ii'' (pBind name1 a (pBind name2 b ctx))
nBlur ii ctx (Plus a b) = trace "blurring plus" $ let (ii', name) = getName ii in do
    c1 <- trace "making inl command" blurSearch ii' (pBind name a ctx)
    c2 <- trace "making inr command" blurSearch ii' (pBind name b ctx)
    return $ MatchPlus (name, c1) (name, c2)
nBlur ii ctx (Minus n) = let (ii', name) = getName ii in
    trace "minusss" $ fmap (MatchMinus name) $ blurSearch ii' (nBind name n ctx)
nBlur ii ctx (PShift n) = let (ii', name) = getName ii in
    trace "lettttt" $ fmap (Let name) $ blurSearch ii' (pBind name (PShift n) ctx)

pFocusSearch :: SearchState -> Context -> PType -> Either Errors Term
pFocusSearch ii ctx ty = trace ("focused search for term " ++ show ty ++ " in ctx\n\t" ++ showCtx ctx) $ checkVar ctx ty <|> case ty of
    Top -> return TT
    PAtomic n -> trace ("no variable found of atomic type " ++ show n) $ Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    Times tA tB -> do
        a <- pFocusSearch ii ctx tA
        b <- pFocusSearch ii ctx tB
        return $ Pair a b
    Plus tA tB -> (trace "trying inL" fmap InL (pFocusSearch ii ctx tA)) <|> trace "trying inr" fmap InR (pFocusSearch ii ctx tB)
    Minus n -> fmap Sub $ nFocusSearch ii ctx n
    PShift nt -> trace ("blurring to construct a term of shifted type " ++ show nt) $ pBlur ii ctx nt
    -- PShift nt -> blur nt

nFocusSearch :: SearchState -> Context -> NType -> Either Errors Coterm
nFocusSearch ii ctx ty = trace ("focused search for coterm " ++ show ty ++ " in ctx\n\t" ++ showCtx ctx) $ checkCovar ctx ty <|> case ty of
    Bot -> return FF
    NAtomic n -> Left $ mkErr $ "Cannot disprove negative atomic " ++ show n
    And tA tB -> fmap PiL (nFocusSearch ii ctx tA) <|> fmap PiR (nFocusSearch ii ctx tB)
    Or tA tB -> trace "$$$$" $ do
        a <- nFocusSearch ii ctx tA
        b <- nFocusSearch ii ctx tB
        return $ Copair a b
    Not p -> fmap Neg $ pFocusSearch ii ctx p
    NShift pt -> trace ("blurring to construct a coterm of shifted type " ++ show pt) nBlur ii ctx pt


main :: IO ()
main = do
    -- let a = Covar (Global "a")
    -- let b = Covar (Global "b")
    let tA = PAtomic (Global "A")
    let ptA = Plus tA (PShift (Not tA))
    -- let nA = NAtomic (Global "A")
    -- let x = Var (Global "x")
    -- print "1"
    -- let res = pCheck emptyCtx (MuOr (Global "a", Global "b") (Connect (Negative (Not tA)) (MuNot (Global "x") (Connect (Positive tA) x a)) b)) (PShift (Or (NShift tA) (Not tA)))
    -- print res
    -- print "2"
    -- let res2 = pCheck emptyCtx (Mu (Global "a") (Connect (Positive ptA) (InR (MuNot (Global "x") (Connect (Positive ptA) (InL x) a))) a)) ptA
    -- print res2
    -- let check3 = cCheck (Connect (Negative (Not tA)) (MuNot (Global "x") (Connect (Positive tA) x a)) b) ([], [(Global "a", NShift tA), (Global "b", Not tA)])
    -- print check3
    putStrLn "CONSTRUCTIVE"
    putStrLn "3"
    let tyconstructive = (PShift (Or (NShift tA) (Not tA)))
    -- -- let tyy = (PShift (Or nA (Not (PShift nA))))
    let res3 = pFocusSearch emptySSt emptyCtx tyconstructive
    print res3
    putStrLn "4"
    let res4 = fmap (\r -> pCheck emptyCtx r tyconstructive) res3
    print res4
    putStrLn "CLASSICAL"
    let tyclassical = PShift (NShift ptA)
    -- let tyclassical = ptA
    print "5"
    let res5 = pFocusSearch emptySSt emptyCtx tyclassical
    print res5
    print "6"
    let res6 = fmap (\r -> pCheck emptyCtx r tyclassical) res5
    print res6
    -- let res3 = step $ Connect (PShift (Or (NShift tA) (Not tA))) Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)
    -- print res3
