{-# LANGUAGE FlexibleInstances #-}
module Ast where
import Control.Applicative
import Data.List (intercalate)

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
    -- | Exists Name PType
    | PShift NType
    deriving Eq

instance Show PType where
    show Top = "T"
    show (PAtomic n) = "+" ++ show n
    show (Plus t1 t2) = "(" ++ show t1 ++ " (+) " ++ show t2 ++ ")"
    show (Times t1 t2) = "(" ++ show t1 ++ " (x) " ++ show t2 ++ ")"
    show (Minus t) = "(-)(" ++ show t ++ ")"
    -- show (Exists n t) = "Exists{" ++ show n ++ "}(" ++ show t ++ ")" 
    show (PShift t) = "up(" ++ show t ++ ")"

data NType = Bot
    | NAtomic Name
    | And NType NType
    | Or NType NType 
    | Not PType
    -- | Forall Name NType
    | NShift PType
    deriving (Eq)

instance Show NType where
    show Bot = "_|_"
    show (NAtomic n) = "-" ++ show n
    show (And t1 t2) = "(" ++ show t1 ++ " & " ++ show t2 ++ ")"
    show (Or t1 t2) = "(" ++ show t1 ++ " or " ++ show t2 ++ ")"
    show (Not t) = "~(" ++ show t ++ ")"
    -- show (Forall n t) = "Forall{" ++ show n ++ "}(" ++ show t ++ ")"
    show (NShift t) = "down(" ++ show t ++ ")"

data Type = Positive PType | Negative NType deriving (Eq)

instance Show Type where
    show (Positive pt) = show pt ++ ":+"
    show (Negative nt) = show nt ++ ":-"

data Term = TT
    | Var Name
    | Pair Term Term
    | InL Term
    | InR Term
    -- | Witness Type Term
    | Sub Coterm
    | MuAnd (Name, Command) (Name, Command)
    | MuOr (Name, Name) Command
    | MuNot Name Command
    -- | MuForall (Name, Name) Command
    | Mu Name Command
    deriving (Eq, Show)

data Coterm = FF
    | Covar Name
    | PiL Coterm
    | PiR Coterm
    | Copair Coterm Coterm
    -- | Counter Type Coterm
    | Neg Term
    | MatchTimes (Name, Name) Command
    | MatchPlus (Name, Command) (Name, Command)
    | MatchMinus Name Command
    -- | MatchExists (Name, Name) Command
    | Let Name Command
    deriving (Eq, Show)

data Termish = Tm Term | Co Coterm

data Command = Connect Type Term Coterm deriving (Eq)

instance Show Command where
    show (Connect ty tm co) = "{" ++ show tm ++ "|" ++ show ty ++ "|" ++ show co ++ "}"

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