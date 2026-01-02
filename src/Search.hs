module Search where

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

data SearchState = SSt Int [(Name, Rule)] (Maybe Name)

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

seen :: Name -> Rule -> SearchState -> Bool
seen n r (SSt _ ns _) = (n, r) `elem` ns

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
-- checkContext ctx = trace "checking for matching pair in context" backtrack helper3 (maxSize ctx)
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

mismatch :: SearchState -> Context -> Maybe (Name, Type)
mismatch _ ([], []) = Nothing
mismatch ii ((_, PShift _):xs, ys) = mismatch ii (xs, ys)
mismatch ii ((xs, (_, NShift _):ys)) = mismatch ii (xs, ys)
mismatch ii ((_, PAtomic _):xs, ys) = mismatch ii (xs, ys)
mismatch ii ((xs, (_, NAtomic _):ys)) = mismatch ii (xs, ys)
-- mismatch _ ((n, pt):_, _) = trace ("+type " ++ show pt ++ " is neither shift nor atomic") $ Just (n, Positive pt)
mismatch _ ((n, pt):_, _) = Just (n, Positive pt)
-- mismatch _ (_, (n, nt):_) = trace ("-type " ++ show nt ++ " is neither shift nor atomic") $ Just (n, Negative nt)
mismatch _ (_, (n, nt):_) = Just (n, Negative nt)

focus :: Int -> Context -> Either Errors (Name, Type)
-- focus k ([], []) = trace "empty" $ Left $ mkErr $ "Cannot focus in empty context" ++ show k
focus k ([], []) = Left $ mkErr $ "Cannot focus in empty context" ++ show k
-- focus 0 ((n, PShift ty):_, _) = trace ("got negative " ++ show n) Right (n, Negative ty)
focus 0 ((n, PShift ty):_, _) = Right (n, Negative ty)
-- focus 0 (_, (n, NShift ty):_) = trace ("got positive " ++ show n) Right (n, Positive ty)
focus 0 (_, (n, NShift ty):_) = Right (n, Positive ty)
focus 0 ctx = Left $ mkErr $ "OH NOOOOOO Non-shifted in context " ++ showCtx ctx ++ " (should be impossible? or not idk)"
-- focus k (_:xs, ys) = trace ("countingleft:" ++ show k) focus (k - 1) (xs, ys)
focus k (_:xs, ys) = focus (k - 1) (xs, ys)
-- focus k ([], _:ys) = trace ("countingright:" ++ show k) $ focus (k - 1) ([], ys)
focus k ([], _:ys) = focus (k - 1) ([], ys)

focuser :: SearchState -> Int -> Context -> Either Errors Command
focuser _ 0 ctx = Left $ mkErr $ "Focused through whole context " ++ showCtx ctx ++ "and got nothing"
-- focuser ii k ctx = trace ("focusing formula " ++ show k ++ " of " ++ show (maxSize ctx) ++ " " ++ showCtx ctx) $ (do
focuser ii k ctx = (do
    pair <- focus (k - 1) ctx
    let (name, ty) = pair
    -- let ii' = trace ("noting " ++ show name) note name ii
    let ii' = note name ii
    case ty of
        -- Positive pt -> trace ("focusing positive " ++ show name ++ ": " ++ show pt ++ "\n\t" ++ showCtx ctx) $ do
        Positive pt -> do
            tm <- pFocusSearch ii' ctx pt
            return $ Connect (Positive pt) tm (Covar name)
        -- Negative nt -> trace ("focusing negative " ++ show name ++ ": " ++ show nt ++ "\n\t" ++ showCtx ctx) $ do
        Negative nt -> do
            co <-  nFocusSearch ii' ctx nt
            return $ Connect (Negative nt) (Var name) co
    ) <|> focuser ii (k - 1) ctx

maxSize :: Context -> Int
maxSize (xs, ys) = length xs + length ys

backtrack :: Alternative f => (Int -> f a) -> Int -> f a
backtrack f 0 = f 0
backtrack f k = f k <|> backtrack f (k - 1)

blurSearch :: SearchState -> Context -> Either Errors Command
-- blurSearch ii ctx = trace ("making a command of type\n\t" ++ showCtx ctx) $ checkContext ctx <|> let res = mismatch ii ctx in trace ("mismatch: " ++ show res ++ "\n\t" ++ showCtx ctx) $ case res of
blurSearch ii ctx = checkContext ctx <|> case mismatch ii ctx of
    -- Nothing -> trace ("focusing in context\n\t" ++ showCtx ctx) $ focuser ii (maxSize ctx) ctx
    Nothing -> focuser ii (maxSize ctx) ctx
    Just (name, ty) -> case ty of
        Positive pt -> do
            -- co <- trace ("getting nBlur " ++ show name ++ ": " ++ show pt ++ " at\n\t" ++ showCtx ctx) $ nBlur ii ctx pt
            co <- nBlur ii ctx pt
            -- return $ trace ("muing positive mismatch " ++ show name) $ Connect (Positive pt) (Var name) co
            return $ Connect (Positive pt) (Var name) co
        Negative nt -> do
            -- tm <- trace ("getting pBlur " ++ show name ++ ": " ++ show nt) $ pBlur ii ctx nt
            tm <- pBlur ii ctx nt
            -- return $ trace "muing negative mismatch" $ Connect (Negative nt) tm (Covar name)
            return $ Connect (Negative nt) tm (Covar name)

pBlur :: SearchState -> Context -> NType -> Either Errors Term
pBlur _ _ Bot = Left $ mkErr "Cannot prove Bot"
-- pBlur _ ctx t@(NAtomic _) = trace "chVar" checkVar ctx (PShift t)
pBlur _ ctx t@(NAtomic _) = checkVar ctx (PShift t)
pBlur ii ctx (And a b) = do
    ii'' <- apply AndR ii
    let (ii', name) = getName ii''
    c1 <- blurSearch ii' (nBind name a ctx)
    c2 <- blurSearch ii' (nBind name b ctx)
    return $ MuAnd (name, c1) (name, c2)
-- pBlur ii ctx (Or a b) = trace "orrr" $ do
pBlur ii ctx (Or a b) = do
    iin <- apply OrR ii
    let (ii', name1) = getName iin
    let (ii'', name2) = getName ii'
    res <- blurSearch ii'' (nBind name1 a (nBind name2 b ctx))
    return $ MuOr (name1, name2) res
-- pBlur ii ctx (Not p) = trace "nottt" $ do
pBlur ii ctx (Not p) = do
    iin <- apply NotR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (pBind name p ctx)
    return $ MuNot name res
-- pBlur ii ctx (NShift p) = trace "double-shifted! mooing" $ do
pBlur ii ctx (NShift p) = do
    iin <- apply ShiftR ii
    let (ii', name) = getName iin
    res <- blurSearch ii' (nBind name (NShift p) ctx)
    return $ Mu name res

nBlur :: SearchState -> Context -> PType -> Either Errors Coterm
nBlur _ _ Top = Left $ mkErr "Cannot disprove Top"
-- nBlur _ ctx t@(PAtomic _) = trace ("checking for covar of type " ++ show t ++ " in ctx\n\t" ++ showCtx ctx) checkCovar ctx (NShift t)
nBlur _ ctx t@(PAtomic _) = checkCovar ctx (NShift t)
nBlur ii ctx (Times a b) = do
    ii' <- apply TimesL ii
    let (ii'', name1) = getName ii'
    let (ii''', name2) = getName ii''
    res <- blurSearch ii''' (pBind name1 a (pBind name2 b ctx))
    return $ MatchTimes (name1, name2) res
-- nBlur ii ctx (Plus a b) = trace "blurring plus" $  do
nBlur ii ctx (Plus a b) = do
    ii'' <- apply PlusL ii
    let (ii', name) = getName ii''
    -- c1 <- trace "making inl command" blurSearch ii' (pBind name a ctx)
    c1 <- blurSearch ii' (pBind name a ctx)
    -- c2 <- trace "making inr command" blurSearch ii' (pBind name b ctx)
    c2 <- blurSearch ii' (pBind name b ctx)
    return $ MatchPlus (name, c1) (name, c2)
-- nBlur ii ctx (Minus n) = trace "minusss" $ do
nBlur ii ctx (Minus n) = do
    ii'' <- apply MinusL ii
    let (ii', name) = getName ii''
    res <- blurSearch ii' (nBind name n ctx)
    return $ (MatchMinus name) res
-- nBlur ii ctx (PShift n) = trace "lettttt" $ do
nBlur ii ctx (PShift n) = do
    ii'' <- apply ShiftL ii
    let (ii', name) = getName ii''
    res <- blurSearch ii' (pBind name (PShift n) ctx)
    return $ Let name res

pFocusSearch :: SearchState -> Context -> PType -> Either Errors Term
-- pFocusSearch ii ctx ty = trace ("focused search for term " ++ show ty ++ " in ctx\n\t" ++ showCtx ctx) $ checkVar ctx ty <|> case ty of
pFocusSearch ii ctx ty = checkVar ctx ty <|> case ty of
    Top -> return TT
    -- PAtomic n -> trace ("no variable found of atomic type " ++ show n) $ Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    PAtomic n -> Left $ mkErr $ "Cannot prove positive atomic " ++ show n
    Times tA tB -> do
        ii' <- apply TimesR ii 
        a <- pFocusSearch ii' ctx tA
        b <- pFocusSearch ii' ctx tB
        return $ Pair a b
    Plus tA tB -> (do
            -- ii' <- trace "trying inL" apply PlusR1 ii
            ii' <- apply PlusR1 ii
            res <- pFocusSearch ii' ctx tA
            return $ InL res     
        )
        <|> 
        (do
            -- ii' <- trace "trying inR" apply PlusR2 ii
            ii' <- apply PlusR2 ii
            res <- pFocusSearch ii' ctx tB
            return $ InR res)
    Minus n -> do
        ii' <- apply MinusR ii
        res <- nFocusSearch ii' ctx n
        return $ Sub res
    -- PShift nt -> trace ("blurring to construct a term of shifted type " ++ show nt) $ pBlur ii ctx nt
    PShift nt -> pBlur ii ctx nt

nFocusSearch :: SearchState -> Context -> NType -> Either Errors Coterm
-- nFocusSearch ii ctx ty = trace ("focused search for coterm " ++ show ty ++ " in ctx\n\t" ++ showCtx ctx) $ checkCovar ctx ty <|> case ty of
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
    -- Or tA tB -> trace "$$$$" $ do
    Or tA tB -> do
        ii' <- apply OrL ii
        a <- nFocusSearch ii' ctx tA
        b <- nFocusSearch ii' ctx tB
        return $ Copair a b
    Not p -> do
        ii' <- apply NotL ii 
        res <- pFocusSearch ii' ctx p
        return $ Neg res 
    -- NShift pt -> trace ("blurring to construct a coterm of shifted type " ++ show pt) nBlur ii ctx pt
    NShift pt -> nBlur ii ctx pt

