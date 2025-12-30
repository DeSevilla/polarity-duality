module Main (main) where

import Debug.Trace (trace)
import Data.Tuple (swap)
import Control.Applicative (Alternative(..))

import Ast
import Check

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

-- checkContext :: Context -> Either Errors Command
-- checkContext ctx = 
--     where
--         helper cx (Positive pt) = do
--             tm <- checkVar cx pt
--             co <- checkCovar cx (NShift pt)
--             return $ Connect (Positive pt) tm co
--         helper cx (Negative nt) = do
--             tm <- checkVar cx (PShift nt)
--             co <- checkCovar cx nt
--             return $ Connect (Negative nt) tm co

mismatch :: Context -> (Context, Maybe (Name, Type))
mismatch ([], []) = (([], []), Nothing)
mismatch (x@(_, PShift _):xs, ys) = case mismatch (xs, ys) of
    ((xs', ys'), res) -> ((x:xs', ys'), res)
mismatch ((xs, y@(_, NShift _):ys)) = case mismatch (xs, ys) of
    ((xs', ys'), res) -> ((xs', y:ys'), res)
mismatch (x@(n, pt):xs, ys) = ((x:xs, ys), Just (n, Positive pt))
mismatch (xs, y@(n, nt):ys) = ((xs, y:ys), Just (n, Negative nt))
-- mismatch ((n, pt):xs, ys) = ((xs, (n, NShift pt):ys), Just (n, Positive pt))
-- mismatch (xs, (n, nt):ys) = (((n, PShift nt):xs, ys), Just (n, Negative nt))
    
-- mismatch :: Context -> (Context, Maybe (Name, Type))
-- mismatch ([], []) = (([], []), Nothing)
-- mismatch ((n, PShift nt):xs, ys) = ((xs, ys), Just (n, Negative nt))
-- mismatch ((xs, (n, NShift pt):ys)) = ((xs, ys), Just (n, Positive pt))
-- mismatch (x:xs, ys) = case mismatch (xs, ys) of
--     ((xs', ys'), res) -> ((x:xs', ys'), res)
-- mismatch (xs, y:ys) = case mismatch (xs, ys) of
--     ((xs', ys'), res) -> ((xs', y:ys'), res)

focus :: Int -> Context -> Either Errors (Context, (Name, Type))
focus k ([], []) = trace "empty" $ Left $ mkErr $ "Cannot focus in empty context" ++ show k
focus 0 ((n, PShift ty):xs, ys) = Right ((xs, ys), (n, Negative ty))
focus 0 (xs, (n, NShift ty):ys) = Right ((xs, ys), (n, Positive ty))
-- focus 0 ((n, PShift ty):xs, ys) = Right ((xs, ys), (n, Negative ty))
-- focus 0 (xs, (n, NShift ty):ys) = Right ((xs, ys), (n, Positive ty))
focus 0 ctx = Left $ mkErr $ "OH NOOOOOO Non-shifted in context " ++ show ctx ++ " (should be impossible)"
focus k (x:xs, ys) = trace ("countingleft:" ++ show k) $ do
    res <- focus (k - 1) (xs, ys)
    let ((xs', ys'), formula) = res
    return $ ((x:xs', ys'), formula)
focus k ([], y:ys) = trace ("countingright:" ++ show k) $ do
    res <- focus (k - 1) ([], ys)
    let ((xs', ys'), formula) = res
    return $ ((xs', y:ys'), formula)
-- focus k (xs, ys)

focuser :: Int -> Int -> Context -> Either Errors Command
focuser _ (-1) ctx = Left $ mkErr $ "Focused through whole context " ++ show ctx ++ "and got nothing"
focuser ii k ctx = trace ("focusing formula " ++ show k ++ " of " ++ show (maxSize ctx) ++ " " ++ show ctx) $ (do
    pair <- focus k ctx
    let (ctx', (name, ty)) = pair
    case ty of
        Positive pt -> fmap (\v -> (Connect (Positive pt) v (Covar name))) $ trace ("focusing positive " ++ show name ++ ": " ++ show pt ++ "\n\t" ++ show ctx ++ "\n\t" ++ show ctx') $ pFocusSearch ii ctx pt
        Negative nt -> fmap (Connect (Negative nt) (Var name)) $ trace ("focusing negative " ++ show name ++ ": " ++ show nt ++ "\n\t" ++ show ctx ++ "\n\t" ++ show ctx') $ nFocusSearch ii ctx nt) <|> focuser ii (k - 1) ctx

maxSize :: Context -> Int
maxSize (xs, ys) = length xs + length ys

-- nonFocuser k = 

backtrack :: Alternative f => (Int -> f a) -> Int -> f a
backtrack f 0 = f 0
backtrack f k = f k <|> backtrack f (k - 1)

-- we need backtracking explicitly here
blurSearch :: Int -> Context -> Either Errors Command
-- blurSearch ii ctx = trace ("making a command of type " ++ show ctx) $ 
blurSearch ii ctx = trace ("making a command of type " ++ show ctx) $ let (ctx', res) = mismatch ctx in trace ("mismatch: " ++ show res ++ "\n\t" ++ show ctx ++ "\n\t" ++ show ctx' ++ "\n....") $ case res of
    Nothing -> trace ("focusing in context " ++ show ctx) $ focuser ii (maxSize ctx) ctx
    -- Just (name, ty) -> 
    Just (name, ty) -> case ty of
        Positive pt -> do
            -- cmd <- trace ("getting positive blur " ++ show name ++ ": " ++ show pt) $ blurSearch ii ctx'
            co <- trace ("getting nBlur " ++ show name ++ ": " ++ show pt ++ " at " ++ show ctx) $ nBlur ii ctx pt
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

pBlur :: Int -> Context -> NType -> Either Errors Term
pBlur _ _ Bot = Left $ mkErr "Cannot prove Bot"
pBlur _ ctx t@(NAtomic _) = trace "chVar" checkVar ctx (PShift t) -- fmap (Mu (Local ii)) $ blurSearch (ii + 1) $ nBind (Local ii) t ctx
pBlur ii ctx (And a b) = do
    c1 <- blurSearch (ii + 1) (pBind (Local ii) (PShift a) ctx)
    c2 <- blurSearch (ii + 1) (pBind (Local ii) (PShift b) ctx)
    return $ MuAnd (Local ii, c1) (Local ii, c2)
pBlur ii ctx (Or a b) = fmap (MuOr (Local ii, Local (ii + 1))) $ blurSearch (ii + 2) (pBind (Local ii) (PShift a) (pBind (Local (ii + 1)) (PShift b) ctx))
pBlur ii ctx (Not p) = trace "nottt" $ fmap (MuNot (Local ii)) $ blurSearch (ii + 1) (pBind (Local ii) p ctx)
pBlur ii ctx (NShift p) = trace "double-shifted! mooing" $ fmap (Mu (Local ii)) $ blurSearch (ii + 1) (nBind (Local ii) (NShift p) ctx)
-- pBlur ctx 

nBlur :: Int -> Context -> PType -> Either Errors Coterm
nBlur _ _ Top = Left $ mkErr "Cannot disprove Top"
nBlur _ ctx t@(PAtomic _) = checkCovar ctx (NShift t)
nBlur ii ctx (Times a b) = fmap (MatchTimes (Local ii, Local (ii + 1))) $ blurSearch (ii + 2) (pBind (Local ii) a (pBind (Local (ii + 1)) b ctx))
nBlur ii ctx (Plus a b) = do
    c1 <- blurSearch (ii + 1) (pBind (Local ii) a ctx)
    c2 <- blurSearch (ii + 1) (pBind (Local ii) b ctx)
    return $ MatchPlus (Local ii, c1) (Local ii, c2)
nBlur ii ctx (Minus n) = trace "minusss" $ fmap (MatchMinus (Local ii)) $ blurSearch (ii + 1) (nBind (Local ii) n ctx)
nBlur ii ctx (PShift n) = trace "lettttt" $ fmap (Let (Local ii)) $ blurSearch (ii + 1) (nBind (Local ii) n ctx)

pFocusSearch :: Int -> Context -> PType -> Either Errors Term
pFocusSearch ii ctx ty = trace ("focused search for +" ++ show ty ++ " in ctx " ++ show ctx) $ checkVar ctx ty <|> case ty of
    Top -> return TT
    PAtomic n -> trace ("no variable found of atomic type" ++ show n) $ Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    Times tA tB -> do
        a <- pFocusSearch ii ctx tA
        b <- pFocusSearch ii ctx tB
        return $ Pair a b
    Plus tA tB -> (trace "trying inL" fmap InL (pFocusSearch ii ctx tA)) <|> trace "trying inr" fmap InR (pFocusSearch ii ctx tB)
    Minus n -> fmap Sub $ nFocusSearch ii ctx n
    PShift nt -> trace "got a shift, blurring" $ pBlur ii ctx nt
    -- PShift nt -> blur nt

nFocusSearch :: Int -> Context -> NType -> Either Errors Coterm
nFocusSearch ii ctx ty = trace ("focused search -" ++ show ty ++ " in ctx " ++ show ctx) $ checkCovar ctx ty <|> case ty of
    Bot -> return FF
    NAtomic n -> Left $ mkErr $ "Cannot disprove negative atomic " ++ show n
    And tA tB -> fmap PiL (nFocusSearch ii ctx tA) <|> fmap PiR (nFocusSearch ii ctx tB)
    Or tA tB -> do
        a <- nFocusSearch ii ctx tA
        b <- nFocusSearch ii ctx tB
        return $ Copair a b
    Not p -> fmap Neg $ pFocusSearch ii ctx p
    NShift pt -> nBlur ii ctx pt


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
    -- print "3"
    -- let tyconstructive = (PShift (Or (NShift tA) (Not tA)))
    -- -- -- let tyy = (PShift (Or nA (Not (PShift nA))))
    -- let res3 = pFocusSearch 0 emptyCtx tyconstructive
    -- print res3
    -- print "4"
    -- let res4 = fmap (\r -> pCheck emptyCtx r tyconstructive) res3
    -- print res4
    let tyclassical = PShift (NShift ptA)
    -- let tyclassical = ptA
    print "5"
    let res5 = pFocusSearch 0 emptyCtx tyclassical
    print res5
    print "6"
    let res6 = fmap (\r -> pCheck emptyCtx r tyclassical) res5
    print res6
    -- let res3 = step $ Connect (PShift (Or (NShift tA) (Not tA))) Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)
    -- print res3
