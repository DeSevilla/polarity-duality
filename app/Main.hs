module Main (main) where

-- data Name = Global String | Local Int deriving (Eq, Show)
type Name = String

data PType = Top
    | PAtomic Name
    | Plus PType PType
    | Times PType PType 
    | Minus NType
    -- | Exists PType Ptype??
    | PShift NType
    deriving (Eq, Show)

data NType = Bot
    | NAtomic Name
    | And NType NType
    | Or NType NType 
    | Not PType
    -- | Forall Ptype Ptype
    | NShift PType
    deriving (Eq, Show)

data Type = Positive PType | Negative NType deriving (Eq, Show)

data Term = TT
    | Var Name
    | Pair Term Term
    | InL Term
    | InR Term
    -- | Exist Type Term
    | Sub Coterm
    | MuAnd (Name, Command) (Name, Command)
    | MuOr (Name, Name) Command
    | MuNot Name Command
    -- | MuExist (Type, Name) Command
    | Mu Name Command
    deriving (Eq, Show)

data Coterm = FF
    | Covar Name
    | PiL Coterm
    | PiR Coterm
    | Copair Coterm Coterm
    -- | Nall Type Coterm
    | Neg Term
    | MatchTimes (Name, Name) Command
    | MatchPlus (Name, Command) (Name, Command)
    | MatchMinus Name Command
    -- | MatchForall (Type, Name) Command
    | Let Name Command
    deriving (Eq, Show)

data Termish = Tm Term | Co Coterm

data Command = Connect Type Term Coterm deriving (Eq, Show)

type Context = ([(Name, PType)], [(Name, NType)])

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

-- pSubst :: Name -> Termish -> Term -> Term
-- pSubst _ _ True = True
-- pSubst n (Tm tm) (Var n') = if n == n' then tm else (Var n')
-- pSubst _ (Co _) (Var _) = undefined  -- TODO handle this better
-- pSubst n tm (Pair a b) = Pair (pSubst n tm a) (pSubst n tm b)
-- pSubst n tm (InL a) = InL (pSubst n tm a)
-- pSubst n tm (InR b) = InR (pSubst n tm b)
-- -- pSubst n tm ()

-- nSubst :: Name -> Termish -> Coterm -> Coterm
-- nSubst _ _ False = False
-- nSubst n (Co ct) (Covar n') = if n == n' then ct else (Covar n')
-- nSubst _ (Tm _) (Covar _) = undefined
-- nSubst n ct (Copair a b) = Copair (nSubst n ct a) (nSubst n ct b)

-- cSubst :: Name -> Termish -> Command -> Command
-- cSubst n tm (Connect ty a b) = Connect ty (pSubst n tm a) (nSubst n tm b)

-- step :: Command -> Command
-- step (Connect _ a b) = case (a, b) of
--     (Pair a1 a2, MatchTimes (n1, n2) c) -> cSubst n2 (Tm a2) (cSubst n1 (Tm a1) c)
--     _ -> undefined



main :: IO ()
main = do
    let a = Covar "a"
    let b = Covar "b"
    let tA = PAtomic "A"
    let x = Var "x"
    let res = pCheck ([], []) (MuOr ("a", "b") (Connect (Negative (Not tA)) (MuNot "x" (Connect (Positive tA) x a)) b)) (PShift (Or (NShift tA) (Not tA)))
    print res
    let ptA = Plus tA (PShift (Not tA))
    let res2 = pCheck ([], []) (Mu "a" (Connect (Positive ptA) (InR (MuNot "x" (Connect (Positive ptA) (InL x) a))) a)) ptA
    print res2
    -- let res3 = step (Connect (Negative (Not tA)) (MuNot "x" (Connect (Positive tA) x a)) b)
    -- print res3
