{-# LANGUAGE FlexibleInstances #-}
module Ast where
import Control.Applicative
import Data.List (intercalate)
import Debug.Trace

data Name = Global String | Local Int deriving (Eq)

instance Show Name where
  show (Global s) = s
  show (Local i) = "L" ++ show i
-- type Name = String

data PType = Top
    | PAtomic Name
    | Plus PType PType
    | Times PType PType 
    | Minus NType
    -- | Exists PType Ptype??
    | PShift NType
    deriving Eq

instance Show PType where
    show Top = "T"
    show (PAtomic n) = "+" ++ show n
    show (Plus t1 t2) = "(" ++ show t1 ++ " (+) " ++ show t2 ++ ")"
    show (Times t1 t2) = "(" ++ show t1 ++ " (x) " ++ show t2 ++ ")"
    show (Minus t) = "(-)(" ++ show t ++ ")"
    show (PShift t) = "up(" ++ show t ++ ")"

data NType = Bot
    | NAtomic Name
    | And NType NType
    | Or NType NType 
    | Not PType
    -- | Forall Ptype Ptype
    | NShift PType
    deriving (Eq)

instance Show NType where
    show Bot = "_|_"
    show (NAtomic n) = "-" ++ show n
    show (And t1 t2) = "(" ++ show t1 ++ " & " ++ show t2 ++ ")"
    show (Or t1 t2) = "(" ++ show t1 ++ " or " ++ show t2 ++ ")"
    show (Not t) = "~(" ++ show t ++ ")"
    show (NShift t) = "down(" ++ show t ++ ")"

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

data SearchState = SSt Int [(Name, Rule)] (Maybe Name)

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

type Context = ([(Name, PType)], [(Name, NType)])

showCtx :: Context -> String
showCtx (xs, ys) = commatize showBinding xs ++ " |- " ++ commatize showBinding ys

showBinding :: (Show a1, Show a2) => (a1, a2) -> String
showBinding (n, t) = show n ++ ":" ++ show t

commatize :: (a -> String) -> [a] -> String
commatize f xs = intercalate ", " (map f xs)

emptyCtx :: Context
emptyCtx = ([], [])

pBind :: Name -> PType -> Context -> Context
pBind name ty (cin, cout) = ((name, ty):cin, cout)

nBind :: Name -> NType -> Context -> Context
nBind name ty (cin, cout) = (cin, (name, ty):cout)

pLookup :: Name -> Context -> Maybe PType
pLookup n (xs, _) = lookup n xs

nLookup :: Name -> Context -> Maybe NType
nLookup n (_, ys) = lookup n ys

data Errors = Errs [String] deriving (Eq, Show)

mkErr :: String -> Errors
mkErr s = Errs [s]

instance Semigroup Errors where
    Errs a <> Errs b = Errs $ a ++ b

instance Monoid Errors where
    mempty = Errs []

instance Alternative (Either Errors) where
    empty = Left mempty

    Right a <|> _ = Right a
    _ <|> (Right b) = Right b
    Left e1 <|> Left e2 = Left $ e1 <> e2