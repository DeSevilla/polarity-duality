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
-- pSubst n tm (Witness t a) = (Witness t (pSubst n tm a))
pSubst n tm (MuAnd (n1, c1) (n2, c2)) = MuAnd (n1, cSubst n tm c1) (n2, cSubst n tm c2)
pSubst n tm (MuOr ns c) = MuOr ns $ cSubst n tm c  -- TODO i think we need renamings
pSubst n tm (MuNot n' c) = MuNot n' $ cSubst n tm c
-- pSubst n tm (MuForall n' c) = MuForall n' $ cSubst n tm c
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
-- nSubst n ct (Counter ty a) = Counter ty (nSubst n ct a)
nSubst n ct (MatchTimes ns c) = MatchTimes ns $ cSubst n ct c -- todo renamings
nSubst n ct (MatchPlus (n1, c1) (n2, c2)) = MatchPlus (n1, cSubst n ct c1) (n2, cSubst n ct c2)
nSubst n ct (MatchMinus n' c) = MatchMinus n' $ cSubst n ct c
-- nSubst n ct (MatchExists n' c) = MatchExists n' $ cSubst n ct c
nSubst n ct (Let n' c) = Let n' $ cSubst n ct c

ptSubst :: Name -> Type -> PType -> PType
ptSubst _ _ Top = Top
ptSubst n (Positive pt) (PAtomic n') = if n == n' then pt else (PAtomic n')
ptSubst n (Negative _) (PAtomic n') = if n == n' then trace ("Tried to subst negative for positive atomic") PAtomic n' else PAtomic n'
ptSubst n t (Plus a b) = Plus (ptSubst n t a) (ptSubst n t b)
ptSubst n t (Times a b) = Times (ptSubst n t a) (ptSubst n t b)
ptSubst n t (Minus a) = Minus $ ntSubst n t a
-- ptSubst n t (Exists n' a) = if n == n' then trace "name collision" ptSubst n t a else Exists n' $ ptSubst n t a
ptSubst n t (PShift a) = PShift $ ntSubst n t a

ntSubst :: Name -> Type -> NType -> NType
ntSubst _ _ Bot = Bot
ntSubst n (Positive _) (NAtomic n') = if n == n' then trace ("Tried to subst positive for negative atomic") NAtomic n' else NAtomic n'
ntSubst n (Negative nt) (NAtomic n') = if n == n' then nt else NAtomic n'
ntSubst n t (Or a b) = Or (ntSubst n t a) (ntSubst n t b)
ntSubst n t (And a b) = And (ntSubst n t a) (ntSubst n t b)
ntSubst n t (Not a) = Not $ ptSubst n t a
-- ntSubst n t (Forall n' a) = if n == n' then trace "name collision" ntSubst n t a else Forall n' $ ntSubst n t a
ntSubst n t (NShift a) = NShift $ ptSubst n t a




cSubst :: Name -> Termish -> Command -> Command
cSubst n tm (Connect ty v e) = Connect ty (pSubst n tm v) (nSubst n tm e)

value :: Term -> Bool
value TT = True
value (Var _) = True
value (Pair a b) = value a && value b
value (InL a) = value a
value (InR b) = value b
value (Sub _) = True
-- value (Witness t a) = value a
value (MuAnd _ _) = True
value (MuOr _ _) = True
value (MuNot _ _) = True
-- value (MuForall _ _) = True -- or should these be false?
value (Mu _ _) = False

covalue :: Coterm -> Bool
covalue FF = True
covalue (Covar _) = True
covalue (Copair a b) = covalue a && covalue b
covalue (PiL a) = covalue a
covalue (PiR b) = covalue b
covalue (Neg _) = True
-- covalue (Counter t a) = covalue a
covalue (MatchTimes _ _) = True
covalue (MatchPlus _ _) = True
covalue (MatchMinus _ _) = True
-- covalue (MatchExists _ _) = True -- TODO or should these be false?
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
