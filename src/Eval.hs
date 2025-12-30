module Eval where
import Ast
import Debug.Trace (trace)


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

value :: Term -> Bool
value TT = True
value (Var _) = True
value (Pair a b) = value a && value b
value (InL a) = value a
value (InR b) = value b
value (Sub _) = True
value (MuAnd _ _) = True
value (MuOr _ _) = True
value (MuNot _ _) = True
value (Mu _ _) = False

covalue :: Coterm -> Bool
covalue FF = True
covalue (Covar _) = True
covalue (Copair a b) = covalue a && covalue b
covalue (PiL a) = covalue a
covalue (PiR b) = covalue b
covalue (Neg _) = True
covalue (MatchTimes _ _) = True
covalue (MatchPlus _ _) = True
covalue (MatchMinus _ _) = True
covalue (Let _ _) = False


-- -- not sure how we'd get the value restriction into this
-- -- also sigma rules require figuring out variable names
-- step :: Command -> Either String Command
-- step (Connect _ (Pair a b) (MatchTimes (n1, n2) c)) = Right $ cSubst n2 (Tm a) (cSubst n1 (Tm b) c)
-- -- step (Connect (Times tA tB) (Pair a b) env) = Connect tA a (Let )
-- step (Connect _ (InL a) (MatchPlus (n1, c1) _)) = Right $ cSubst n1 (Tm a) c1
-- step (Connect _ (InR b) (MatchPlus _ (n2, c2))) = Right $ cSubst n2 (Tm b) c2
-- step (Connect _ (Sub ct) (MatchMinus n c)) = Right $ cSubst n (Co ct) c
-- step (Connect _ (MuAnd (n1, c1) _) (PiL a)) = Right $ cSubst n1 (Co a) c1
-- step (Connect _ (MuAnd _ (n2, c2)) (PiR b)) = Right $ cSubst n2 (Co b) c2
-- step (Connect _ (MuOr (n1, n2) c) (Copair a b)) = Right $ cSubst n2 (Co a) (cSubst n1 (Co b) c)
-- step (Connect _ (MuNot n c) (Neg tm)) = Right $ cSubst n (Tm tm) c
-- step (Connect (Positive _) (Mu n c) ct) = Right $ cSubst n (Co ct) c
-- step (Connect (Positive _) tm (Let n c)) = Right $ cSubst n (Tm tm) c
-- step (Connect (Negative _) tm (Let n c)) = Right $ cSubst n (Tm tm) c
-- step (Connect (Negative _) (Mu n c) ct) = Right $ cSubst n (Co ct) c
-- step c = Left $ "Could not step command " ++ show c
