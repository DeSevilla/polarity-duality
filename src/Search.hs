module Search (termSearch, cotermSearch) where

import Data.Tuple (swap)
import Control.Applicative (Alternative(..))
import Ast
import Control.Monad ((>=>))

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

backtrack :: Alternative f => Int -> (Int -> f a) -> f a
backtrack 0 f = f 0
backtrack k f = f k <|> backtrack (k - 1) f

-- throughCtx :: Alternative f => Context -> (Context -> Int -> f a) -> f a
throughCtx :: Alternative f => Context -> (Context -> Int -> f a) -> f a
throughCtx ctx f = backtrack (maxSize ctx) (f ctx)

-- contains: number of binders, list of rules + variables they've been applied to, name currently focused on.
-- might be overcomplicated? can we do this with more just contexts, somehow?
data SearchState = SSt Int [(Name, Rule)] (Maybe Name) deriving (Eq, Show)

emptySSt :: SearchState
emptySSt = SSt 0 [] Nothing

getName :: SearchState -> (SearchState, Name)
getName (SSt ii ns n) = (SSt (ii + 1) ns n, Local ii)

note :: Name -> SearchState -> SearchState
note n (SSt ii ns _) = SSt ii ns (Just n)

-- apply a rule to a variable, eliminating that possibility from contention
apply :: Rule -> SearchState -> Either Errors SearchState
apply r (SSt ii ns (Just n))
    | (n, r) `elem` ns = Left $ mkErr $ "already filling variable " ++ show n ++ " with rule " ++ show r
    | otherwise = Right $ SSt ii ((n, r):ns) Nothing
apply _ sst = Right sst

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

-- TODO I think this does twice as much work as it needs to -- could just scan one section of ctx
findCut :: Context -> Either Errors Command
findCut ctx = throughCtx ctx $ \c -> typeAtIndex c >=> makeCmdOnType c
    where
        typeAtIndex :: Context -> Int -> Either Errors Type
        typeAtIndex = mapCtxIndex makePositive makeNegative

        makePositive (_, t) = return $ Positive t
        makeNegative (_, t) = return $ Negative t

        makeCmdOnType :: Context -> Type -> Either Errors Command
        makeCmdOnType cx (Positive pt) = do
            tm <- checkVar cx pt
            co <- checkCovar cx (NShift pt)
            return $ Connect (Positive pt) tm co
        makeCmdOnType cx (Negative nt) = do
            tm <- checkVar cx (PShift nt)
            co <- checkCovar cx nt
            return $ Connect (Negative nt) tm co

focuser :: SearchState -> Context -> Int -> Either Errors Command
focuser _ ctx 0 = Left $ mkErr $ "Focused through whole context " ++ showCtx ctx ++ "and got nothing"
focuser ii ctx k = do
    (name, ty) <- focus ctx (k - 1)
    let ii' = note name ii
    case ty of
        Positive pt -> do
            tm <- pFocusSearch ii' ctx pt
            return $ Connect (Positive pt) tm (Covar name)
        Negative nt -> do
            co <- nFocusSearch ii' ctx nt
            return $ Connect (Negative nt) (Var name) co
    where
        focus :: Context -> Int -> Either Errors (Name, Type)
        focus = mapCtxIndex posCanFocus negCanFocus

        posCanFocus (n, (PShift ty)) = Right (n, Negative ty)
        posCanFocus _ = Left $ mkErr $ "got non-shifted " ++ show k ++ " in context " ++ showCtx ctx ++ " (caused by backtracking)"

        negCanFocus (n, (NShift ty)) = Right (n, Positive ty)
        negCanFocus _ = Left $ mkErr $ "got non-shifted " ++ show k ++ " in context " ++ showCtx ctx ++ " (caused by backtracking)"

-- find a place where an invertible rule can be applied
-- TODO i think this is doing excess work if there are no mismatches
findInvertible :: SearchState -> Context -> Int -> Either Errors Command
findInvertible _ _ 0 = Left $ mkErr "findMismatch: all our backtracking failed"
findInvertible ii ctx k = do
    (name, ty) <- mismatchAt ctx (k - 1)
    case ty of
        Positive pt -> do
            let ii' = note name ii
            co <- pConsume ii' ctx pt
            return $ Connect (Positive pt) (Var name) co
        Negative nt -> do
            let ii' = note name ii
            tm <- nConsume ii' ctx nt
            return $ Connect (Negative nt) tm (Covar name)
        -- Nothing -> Left $ mkErr $ "no mismatches at " ++ show k
    where
        -- positive type on left of sequent or negative type on right
        mismatchAt :: Context -> Int -> Either Errors (Name, Type)
        mismatchAt = mapCtxIndex phelper nhelper

        phelper (n, PShift _) = Left $ mkErr $ "No mismatch at " ++ show n ++ " (+shifted)"
        phelper (n, PAtomic _) = Left $ mkErr $ "No mismatch at " ++ show n ++ " (+atomic)"
        phelper (n, pt) = Right $ (n, Positive pt)

        nhelper (n, NShift _) = Left $ mkErr $ "No mismatch at " ++ show n ++ " (+shifted)"
        nhelper (n, NAtomic _) = Left $ mkErr $ "No mismatch at " ++ show n ++ " (+atomic)"
        nhelper (n, nt) = Right $ (n, Negative nt)


-- negative-inversion phase of the search
-- build mu terms to extract negative types
nConsume :: SearchState -> Context -> NType -> Either Errors Term
nConsume _ _ Btm = Left $ mkErr "Cannot prove Btm"
nConsume _ ctx t@(NAtomic _) = checkVar ctx (PShift t)
nConsume ii ctx (And a b) = do
    ii'' <- apply AndR ii
    let (ii', name) = getName ii''
    c1 <- blurSearch ii' (nBind name a ctx)
    c2 <- blurSearch ii' (nBind name b ctx)
    return $ MuAnd (name, c1) (name, c2)
nConsume ii ctx (Or a b) = do
    ii' <- apply OrR ii
    let (ii'', name1) = getName ii'
    let (ii''', name2) = getName ii''
    res <- blurSearch ii''' (nBind name1 a (nBind name2 b ctx))
    return $ MuOr (name1, name2) res
nConsume ii ctx (Not p) = do
    iin <- apply NotR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (pBind name p ctx)
    return $ MuNot name res
nConsume ii ctx (NShift p) = do
    iin <- apply ShiftR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (nBind name (NShift p) ctx)
    return $ Mu name res

-- positive-inversion phase of the search
-- build mu-tilde coterms to consume positive types
pConsume :: SearchState -> Context -> PType -> Either Errors Coterm
pConsume _ _ Top = Left $ mkErr "Cannot disprove Top"
pConsume _ ctx t@(PAtomic _) = checkCovar ctx (NShift t)
pConsume ii ctx (Times a b) = do
    ii' <- apply TimesL ii
    let (ii'', name1) = getName ii'
    let (ii''', name2) = getName ii''
    res <- blurSearch ii''' (pBind name1 a (pBind name2 b ctx))
    return $ MatchTimes (name1, name2) res
pConsume ii ctx (Plus a b) = do
    ii' <- apply PlusL ii
    let (ii'', name) = getName ii'
    c1 <- blurSearch ii'' (pBind name a ctx)
    c2 <- blurSearch ii'' (pBind name b ctx)
    return $ MatchPlus (name, c1) (name, c2)
pConsume ii ctx (Minus n) = do
    ii' <- apply MinusL ii
    let (ii'', name) = getName ii'
    res <- blurSearch ii'' (nBind name n ctx)
    return $ (MatchMinus name) res
pConsume ii ctx (PShift n) = do
    ii' <- apply ShiftL ii
    let (ii'', name) = getName ii'
    res <- blurSearch ii'' (pBind name (PShift n) ctx)
    return $ Let name res

-- positive-focused phase of the proof search
-- build a term to fill a positive type
-- maintains focus on subterms
pFocusSearch :: SearchState -> Context -> PType -> Either Errors Term
pFocusSearch ii ctx ty = checkVar ctx ty <|> case ty of
    Top -> return TT
    PAtomic n -> Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    Times tA tB -> do
        ii' <- apply TimesR ii
        a <- pFocusSearch ii' ctx tA
        b <- pFocusSearch ii' ctx tB
        return $ Pair a b
    Plus tA tB ->
        (do
            ii' <- apply PlusR1 ii
            res <- pFocusSearch ii' ctx tA
            return $ InL res)
        <|>
        (do
            ii' <- apply PlusR2 ii
            res <- pFocusSearch ii' ctx tB
            return $ InR res)
    Minus n -> do
        ii' <- apply MinusR ii
        res <- nFocusSearch ii' ctx n
        return $ Sub res
    PShift nt -> nConsume ii ctx nt

-- negative-focused phase of the proof search
-- build a coterm to fill a negative type
-- maintains focus on subterms
nFocusSearch :: SearchState -> Context -> NType -> Either Errors Coterm
nFocusSearch ii ctx ty = checkCovar ctx ty <|> case ty of
    Btm -> return FF
    NAtomic n -> Left $ mkErr $ "Cannot disprove negative atomic " ++ show n
    And tA tB ->
        (do
            ii' <- apply AndL1 ii
            res <- (nFocusSearch ii' ctx tA)
            return $ PiL res)
        <|>
        (do
            ii' <- apply AndL2 ii
            res <- nFocusSearch ii' ctx tB
            return $ PiR res)
    Or tA tB -> do
        ii' <- apply OrL ii
        a <- nFocusSearch ii' ctx tA
        b <- nFocusSearch ii' ctx tB
        return $ Copair a b
    Not p -> do
        ii' <- apply NotL ii
        res <- pFocusSearch ii' ctx p
        return $ Neg res
    NShift pt -> pConsume ii ctx pt

termSearch :: PType -> Either Errors Term
termSearch = pFocusSearch emptySSt emptyCtx

cotermSearch :: NType -> Either Errors Coterm
cotermSearch = nFocusSearch emptySSt emptyCtx

-- build a command in a context -- this is generalized focusing
-- 1. check if you can just cut it (TODO is this needed?)
-- 2. if you can apply an invertible rule, apply one
-- 3. if no invertible rules are applicable, pick something to focus on
blurSearch :: SearchState -> Context -> Either Errors Command
blurSearch ii ctx = findCut ctx <|> throughCtx ctx (findInvertible ii) <|> throughCtx ctx (focuser ii)

