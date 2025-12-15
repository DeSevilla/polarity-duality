module Main (main) where

import Ast
import Debug.Trace (trace)

emptyCtx :: Context 
emptyCtx = ([], [])

pBind :: Name -> PType -> Context -> Context
pBind name ty (cin, cout) = ((name, ty):cin, cout)

nBind :: Name -> NType -> Context -> Context
nBind name ty (cin, cout) = (cin, (name, ty):cout)

pCheck :: Context -> Term -> PType -> Either String ()
pCheck ctx (Var n) ty = case lookup n (fst ctx) of
    Just ty' -> if ty == ty' then Right () else Left "Ascribed bad type"
    Nothing -> Left $ "Variable " ++ show n ++ " not found in pCheck at ctx" ++ show ctx
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
pCheck ctx tm ty = Left $ "Could not type " ++ show tm ++ ": " ++ show ty ++ "at context " ++ show ctx
-- pCheck _ _ _ = Left "Not implemented or not real!"

nCheck :: Context -> Coterm -> NType -> Either String ()
nCheck ctx (Covar n) ty = case lookup n (snd ctx) of
    Just ty' -> if ty == ty' then Right () else Left "Ascribed bad type"
    Nothing -> Left $ "Covariable " ++ show n ++ " not found in nCheck at ctx" ++ show ctx
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
nCheck ctx tm ty = Left $ "Could not type " ++ show tm ++ ": " ++ show ty ++ "at context " ++ show ctx


cCheck :: Command -> Context -> Either String ()
cCheck (Connect (Positive t) v e) ctx = do
    pCheck ctx v t
    nCheck ctx e (NShift t)
cCheck (Connect (Negative t) v e) ctx = do
    pCheck ctx v (PShift t)
    nCheck ctx e t

pSubst :: Name -> Termish -> Term -> Term
pSubst _ _ TT = TT
pSubst n (Tm tm) (Var n') = if n == n' then tm else (Var n')
pSubst n (Co ct) (Var n') = if n == n' then trace ("Tried to subst coterm " ++ show ct ++ " into var " ++ show n) (Var n') else Var n'
pSubst n tm (Pair a b) = Pair (pSubst n tm a) (pSubst n tm b)
pSubst n tm (InL a) = InL $ pSubst n tm a
pSubst n tm (InR b) = InR $ pSubst n tm b
pSubst n tm (Sub ct) = Sub $ nSubst n tm ct
pSubst n tm (MuAnd (n1, c1) (n2, c2)) = MuAnd (n1, cSubst n tm c1) (n2, cSubst n tm c2)
pSubst n tm (MuOr ns c) = MuOr ns $ cSubst n tm c
pSubst n tm (MuNot n' c) = MuNot n' $ cSubst n tm c
pSubst n tm (Mu n' c) = Mu n' $ cSubst n tm c
-- pSubst n tm ()

nSubst :: Name -> Termish -> Coterm -> Coterm
nSubst _ _ FF = FF
nSubst n (Co ct) (Covar n') = if n == n' then ct else (Covar n')
nSubst n (Tm tm) (Covar n') = if n == n' then trace ("Tried to subst term " ++ show tm ++ " into covar " ++ show n) (Covar n') else Covar n'
nSubst n ct (Copair a b) = Copair (nSubst n ct a) (nSubst n ct b)
nSubst n ct (PiL a) = PiL $ nSubst n ct a
nSubst n ct (PiR b) = PiR $ nSubst n ct b
nSubst n ct (Neg tm) = Neg $ pSubst n ct tm
nSubst n ct (MatchTimes ns c) = MatchTimes ns $ cSubst n ct c
nSubst n ct (MatchPlus (n1, c1) (n2, c2)) = MatchPlus (n1, cSubst n ct c1) (n2, cSubst n ct c2)
nSubst n ct (MatchMinus n' c) = MatchMinus n' $ cSubst n ct c
nSubst n ct (Let n' c) = Let n' $ cSubst n ct c

cSubst :: Name -> Termish -> Command -> Command
cSubst n tm (Connect ty v e) = Connect ty (pSubst n tm v) (nSubst n tm e)

-- not sure how we'd get the value restriction into this
-- also sigma rules require figuring out variable names
step :: Command -> Either String Command
step (Connect _ (Pair a b) (MatchTimes (n1, n2) c)) = Right $ cSubst n2 (Tm a) (cSubst n1 (Tm b) c)
-- step (Connect (Times tA tB) (Pair a b) env) = Connect tA a (Let )
step (Connect _ (InL a) (MatchPlus (n1, c1) _)) = Right $ cSubst n1 (Tm a) c1
step (Connect _ (InR b) (MatchPlus _ (n2, c2))) = Right $ cSubst n2 (Tm b) c2
step (Connect _ (Sub ct) (MatchMinus n c)) = Right $ cSubst n (Co ct) c
step (Connect _ (MuAnd (n1, c1) _) (PiL a)) = Right $ cSubst n1 (Co a) c1
step (Connect _ (MuAnd _ (n2, c2)) (PiR b)) = Right $ cSubst n2 (Co b) c2
step (Connect _ (MuOr (n1, n2) c) (Copair a b)) = Right $ cSubst n2 (Co a) (cSubst n1 (Co b) c)
step (Connect _ (MuNot n c) (Neg tm)) = Right $ cSubst n (Tm tm) c
step (Connect (Positive _) (Mu n c) ct) = Right $ cSubst n (Co ct) c
step (Connect (Positive _) tm (Let n c)) = Right $ cSubst n (Tm tm) c
step (Connect (Negative _) tm (Let n c)) = Right $ cSubst n (Tm tm) c
step (Connect (Negative _) (Mu n c) ct) = Right $ cSubst n (Co ct) c
step c = Left $ "Could not step command " ++ show c

main :: IO ()
main = do
    let a = Covar "a"
    let b = Covar "b"
    let tA = PAtomic "A"
    let x = Var "x"
    let res = pCheck emptyCtx (MuOr ("a", "b") (Connect (Negative (Not tA)) (MuNot "x" (Connect (Positive tA) x a)) b)) (PShift (Or (NShift tA) (Not tA)))
    print res
    let ptA = Plus tA (PShift (Not tA))
    let res2 = pCheck emptyCtx (Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)) ptA
    print res2
    let check3 = cCheck (Connect (Negative (Not tA)) (MuNot "x" (Connect (Positive tA) x a)) b) ([("x", tA)], [("a", NShift tA), ("b", Not tA)])
    print check3
    let res3 = step (Connect (Negative (Not tA)) (MuNot "x" (Connect (Positive tA) x a)) b)
    print res3
