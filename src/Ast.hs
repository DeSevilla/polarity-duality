module Ast where
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

