module Search (termSearch, cotermSearch) where

import Data.Tuple (swap)
import Control.Applicative (Alternative(..))
import Ast

data Rule = VarR
    | VarL
    | Cut
    | TimesR
    | TimesL
    | PlusR1
    | PlusR2
    | PlusL
    | MinusL
    | MinusR
    | AndL1
    | AndL2
    | AndR
    | OrL
    | OrR
    | NotL 
    | NotR
    | ShiftL
    | ShiftR
    deriving (Eq, Show)

data SearchState = SSt Int [(Name, Rule)] (Maybe Name) deriving (Eq, Show)

emptySSt :: SearchState
emptySSt = SSt 0 [] Nothing

getName :: SearchState -> (SearchState, Name)
getName (SSt ii ns n) = (SSt (ii + 1) ns n, Local ii)

note :: Name -> SearchState -> SearchState
note n (SSt ii ns _) = SSt ii ns (Just n)


apply :: Rule -> SearchState -> Either Errors SearchState
apply r (SSt ii ns (Just n))
    | (n, r) `elem` ns = Left $ mkErr $ "already filling variable " ++ show n ++ " with rule " ++ show r
    | otherwise = Right $ SSt ii ((n, r):ns) Nothing
apply _ sst = Right sst

-- seen :: Name -> Rule -> SearchState -> Bool
-- seen n r (SSt _ ns _) = (n, r) `elem` ns

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
checkContext ctx = backtrack helper3 (maxSize ctx)
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

mismatch :: SearchState -> Int -> Context -> Maybe (Name, Type)
mismatch _ _ ([], []) = Nothing
mismatch _ 0 ((_, PShift _):_, _) = Nothing -- mismatch ii 0 (xs, ys)
mismatch _ 0 ((_, (_, NShift _):_)) = Nothing -- mismatch ii 0 (xs, ys)
mismatch _ 0 ((_, PAtomic _):_, _) = Nothing -- mismatch ii 0 (xs, ys)
mismatch _ 0 ((_, (_, NAtomic _):_)) = Nothing -- mismatch ii 0 (xs, ys)
mismatch _ 0 ((n, pt):_, _) = Just (n, Positive pt)
mismatch _ 0 (_, (n, nt):_) = Just (n, Negative nt)
mismatch ii k (_:xs, ys) = mismatch ii (k - 1) (xs, ys)
mismatch ii k ([], _:ys) = mismatch ii (k - 1) ([], ys)

focus :: Int -> Context -> Either Errors (Name, Type)
focus k ([], []) = Left $ mkErr $ "Cannot focus in empty context" ++ show k
focus 0 ((n, PShift ty):_, _) = Right (n, Negative ty)
focus 0 (_, (n, NShift ty):_) = Right (n, Positive ty)
focus 0 ctx = Left $ mkErr $ "got non-shifted in context " ++ showCtx ctx ++ " (caused by backtracking)"
focus k (_:xs, ys) = focus (k - 1) (xs, ys)
focus k ([], _:ys) = focus (k - 1) ([], ys)

focuser :: SearchState -> Int -> Context -> Either Errors Command
focuser _ 0 ctx = Left $ mkErr $ "Focused through whole context " ++ showCtx ctx ++ "and got nothing"
focuser ii k ctx = (do
    pair <- focus (k - 1) ctx
    let (name, ty) = pair
    let ii' = note name ii
    case ty of
        Positive pt -> do
            tm <- pFocusSearch ii' ctx pt
            return $ Connect (Positive pt) tm (Covar name)
        Negative nt -> do
            co <-  nFocusSearch ii' ctx nt
            return $ Connect (Negative nt) (Var name) co
    ) <|> focuser ii (k - 1) ctx

maxSize :: Context -> Int
maxSize (xs, ys) = length xs + length ys

backtrack :: Alternative f => (Int -> f a) -> Int -> f a
backtrack f 0 = f 0
backtrack f k = f k <|> backtrack f (k - 1)

handler :: SearchState -> Context -> Maybe (Name, Type) -> Either Errors Command
handler ii ctx Nothing = focuser ii (maxSize ctx) ctx
handler ii ctx (Just (name, Positive pt)) = do
    let ii' = note name ii
    co <- nBlur ii' ctx pt
    return $ Connect (Positive pt) (Var name) co
handler ii ctx (Just (name, Negative nt)) = do
    let ii' = note name ii
    tm <- pBlur ii' ctx nt
    return $ Connect (Negative nt) tm (Covar name)

blurrer :: SearchState -> Context -> Int -> Either Errors Command
blurrer _ _ 0 = Left $ mkErr "all our backtracking failed"
blurrer ii ctx k = let res = mismatch ii (k - 1) ctx in
    handler ii ctx res <|> blurrer ii ctx (k - 1)

blurSearch :: SearchState -> Context -> Either Errors Command
blurSearch ii ctx = checkContext ctx <|> blurrer ii ctx (maxSize ctx)

pBlur :: SearchState -> Context -> NType -> Either Errors Term
pBlur _ _ Bot = Left $ mkErr "Cannot prove Bot"
pBlur _ ctx t@(NAtomic _) = checkVar ctx (PShift t)
pBlur ii ctx (And a b) = do
    ii'' <- apply AndR ii
    let (ii', name) = getName ii''
    c1 <- blurSearch ii' (nBind name a ctx)
    c2 <- blurSearch ii' (nBind name b ctx)
    return $ MuAnd (name, c1) (name, c2)
pBlur ii ctx (Or a b) = do
    iin <- apply OrR ii
    let (ii', name1) = getName iin
    let (ii'', name2) = getName ii'
    res <- blurSearch ii'' (nBind name1 a (nBind name2 b ctx))
    return $ MuOr (name1, name2) res
pBlur ii ctx (Not p) = do
    iin <- apply NotR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (pBind name p ctx)
    return $ MuNot name res
pBlur ii ctx (NShift p) = do
    iin <- apply ShiftR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (nBind name (NShift p) ctx)
    return $ Mu name res

nBlur :: SearchState -> Context -> PType -> Either Errors Coterm
nBlur _ _ Top = Left $ mkErr "Cannot disprove Top"
nBlur _ ctx t@(PAtomic _) = checkCovar ctx (NShift t)
nBlur ii ctx (Times a b) = do
    ii' <- apply TimesL ii
    let (ii'', name1) = getName ii'
    let (ii''', name2) = getName ii''
    res <- blurSearch ii''' (pBind name1 a (pBind name2 b ctx))
    return $ MatchTimes (name1, name2) res
nBlur ii ctx (Plus a b) = do
    ii'' <- apply PlusL ii
    let (ii', name) = getName ii''
    c1 <- blurSearch ii' (pBind name a ctx)
    c2 <- blurSearch ii' (pBind name b ctx)
    return $ MatchPlus (name, c1) (name, c2)
nBlur ii ctx (Minus n) = do
    ii'' <- apply MinusL ii
    let (ii', name) = getName ii''
    res <- blurSearch ii' (nBind name n ctx)
    return $ (MatchMinus name) res
nBlur ii ctx (PShift n) = do
    ii'' <- apply ShiftL ii
    let (ii', name) = getName ii''
    res <- blurSearch ii' (pBind name (PShift n) ctx)
    return $ Let name res

pFocusSearch :: SearchState -> Context -> PType -> Either Errors Term
pFocusSearch ii ctx ty = checkVar ctx ty <|> case ty of
    Top -> return TT
    PAtomic n -> Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    Times tA tB -> do
        ii' <- apply TimesR ii 
        a <- pFocusSearch ii' ctx tA
        b <- pFocusSearch ii' ctx tB
        return $ Pair a b
    Plus tA tB -> (do
            ii' <- apply PlusR1 ii
            res <- pFocusSearch ii' ctx tA
            return $ InL res     
        )
        <|> 
        (do
            ii' <- apply PlusR2 ii
            res <- pFocusSearch ii' ctx tB
            return $ InR res)
    Minus n -> do
        ii' <- apply MinusR ii
        res <- nFocusSearch ii' ctx n
        return $ Sub res
    PShift nt -> pBlur ii ctx nt

nFocusSearch :: SearchState -> Context -> NType -> Either Errors Coterm
nFocusSearch ii ctx ty = checkCovar ctx ty <|> case ty of
    Bot -> return FF
    NAtomic n -> Left $ mkErr $ "Cannot disprove negative atomic " ++ show n
    And tA tB -> (do
        ii' <- apply AndL1 ii
        res <- (nFocusSearch ii' ctx tA)
        return $ PiL res
        ) 
        <|> (do
        ii' <- apply AndL2 ii
        res <- nFocusSearch ii' ctx tB
        return $ PiR res
        )
    Or tA tB -> do
        ii' <- apply OrL ii
        a <- nFocusSearch ii' ctx tA
        b <- nFocusSearch ii' ctx tB
        return $ Copair a b
    Not p -> do
        ii' <- apply NotL ii 
        res <- pFocusSearch ii' ctx p
        return $ Neg res 
    NShift pt -> nBlur ii ctx pt

termSearch :: PType -> Either Errors Term
termSearch = pFocusSearch emptySSt emptyCtx

cotermSearch :: NType -> Either Errors Coterm
cotermSearch = nFocusSearch emptySSt emptyCtx