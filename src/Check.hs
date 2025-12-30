module Check where
import Ast


pCheck :: Context -> Term -> PType -> Either Errors ()
pCheck ctx (Var n) ty = case pLookup n ctx of
    Just ty' -> if ty == ty' then Right () else Left $ mkErr "Ascribed bad type"
    Nothing -> Left $ mkErr $ "Variable " ++ show n ++ " not found in pCheck at ctx" ++ show ctx
pCheck ctx (Pair a b) (Times x y) = do
    pCheck ctx a x
    pCheck ctx b y
pCheck ctx (InL a) (Plus x _) = pCheck ctx a x
pCheck ctx (InR b) (Plus _ y) = pCheck ctx b y
pCheck ctx (Sub a) (Minus x) = nCheck ctx a x
pCheck ctx (MuAnd (n1, c1) (n2, c2)) (PShift (And x y)) = do
    cCheck c1 (nBind n1 x ctx)
    cCheck c2 (nBind n2 y ctx)
pCheck ctx (MuOr (n1, n2) c) (PShift (Or x y)) = cCheck c (nBind n1 x (nBind n2 y ctx))
pCheck ctx (MuNot n c) (PShift (Not t)) = cCheck c (pBind n t ctx)
pCheck ctx (Mu n c) (PShift ty) = cCheck c (nBind n ty ctx)
pCheck ctx (Mu n c) ty = cCheck c (nBind n (NShift ty) ctx)
pCheck _ TT Top = Right ()
pCheck ctx tm ty = Left $ mkErr $ "Could not type " ++ show tm ++ ": " ++ show ty ++ "at context " ++ show ctx
-- pCheck _ _ _ = Left "Not implemented or not real!"

nCheck :: Context -> Coterm -> NType -> Either Errors ()
nCheck ctx (Covar n) ty = case nLookup n ctx of
    Just ty' -> if ty == ty' then Right () else Left $ mkErr $ "Ascribed bad type"
    Nothing -> Left $ mkErr $ "Covariable " ++ show n ++ " not found in nCheck at ctx" ++ show ctx
nCheck ctx (PiL a) (And x _) = nCheck ctx a x
nCheck ctx (PiR b) (And _ y) = nCheck ctx b y
nCheck ctx (Copair a b) (Or x y) = do
    nCheck ctx a x
    nCheck ctx b y
nCheck ctx (Neg a) (Not x) = pCheck ctx a x
nCheck ctx (MatchTimes (n1, n2) c) (NShift (Times x y)) = cCheck c (pBind n1 x (pBind n2 y ctx))
nCheck ctx (MatchPlus (n1, c1) (n2, c2)) (NShift (Plus x y)) = do
    cCheck c1 (pBind n1 x ctx)
    cCheck c2 (pBind n2 y ctx)
nCheck ctx (MatchMinus n c) (NShift (Minus t)) = cCheck c (nBind n t ctx)
nCheck ctx (Let n c) (NShift ty) = cCheck c (pBind n ty ctx)
nCheck ctx (Let n c) ty = cCheck c (pBind n (PShift ty) ctx)
nCheck _ FF Bot = Right ()
nCheck ctx tm ty = Left $ mkErr $ "Could not type " ++ show tm ++ ": " ++ show ty ++ "at context " ++ show ctx


cCheck :: Command -> Context -> Either Errors ()
cCheck (Connect (Positive t) v e) ctx = do
    pCheck ctx v t
    nCheck ctx e (NShift t)
cCheck (Connect (Negative t) v e) ctx = do
    pCheck ctx v (PShift t)
    nCheck ctx e t