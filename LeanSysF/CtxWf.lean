
import LeanSubst
import LeanSysF.Term
import LeanSysF.Kinding

open LeanSubst

inductive CtxWf : Ctx Term -> Prop where
| nil : CtxWf []
| cons :
  Γ ⊢ A type ->
  CtxWf Γ ->
  CtxWf (A::Γ)

notation:170 "⊢ " Γ:170 => CtxWf Γ
