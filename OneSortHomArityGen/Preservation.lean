import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding
import OneSortHomArityGen.Typing
import OneSortHomArityGen.Reduction
import OneSortHomArityGen.Progress

namespace OneSortHomArityGen

open LeanSubst

theorem preservation_step : Γ ⊢ t : A -> t ~> t' -> Γ ⊢ t' : A := by
  intro j r
  induction j generalizing t'
  case var => cases r
  case app Γ A B f a j1 j2 ih1 ih2 =>
    generalize zdef : f :@ a = z at *
    cases r; all_goals try solve | cases zdef
    case beta A' b' t' =>
      injection zdef with _ _ e; simp at e
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      replace j1 := Typing.lam_inv j1
      replace j1 := Typing.beta j1 j2; simp at j1
      apply j1
    case ctor v i ts ts' h r =>
      injection zdef with e1 e2 e3; subst e1 e2 e3; simp at *
      cases i using Fin.cases2
      case _ =>
        simp at *; subst h
        replace ih1 := ih1 r
        rw [<-Vec.eta2 (t := ts')]
        apply Typing.app ih1 j2
      case _ i =>
        simp at *; subst h
        replace ih2 := ih2 r
        rw [<-Vec.eta2 (t := ts')]
        apply Typing.app j1 ih2
  case lam Γ A B t j1 j2 ih =>
    cases r
    case bind1 i ts h r =>
      cases i; case _ i p =>
      cases i <;> simp at *
      case _ =>
        have lem := Kinding.value j1
        exfalso; apply Value.sound lem _ r
      case _ n => simp at p
    case bind2 t' r =>
      replace ih := ih r
      apply Typing.lam j1 ih
  case tapp Γ P P' f a j1 j2 j3 ih =>
    generalize zdef : f :@[a] = z at *
    cases r; all_goals try solve | cases zdef
    case tbeta b' t' =>
      injection zdef with _ _ e; simp at e
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j1; case _ j1 =>
      have lem := Typing.beta_type j1 j2
      subst j3; apply lem
    case ctor v i ts ts' h r =>
      injection zdef with e1 e2 e3; subst e1 e2 e3; simp at *
      cases i using Fin.cases2
      case _ =>
        simp at *; subst h
        replace ih := ih r
        rw [<-Vec.eta2 (t := ts')]
        apply Typing.tapp ih j2 j3
      case _ =>
        simp at r
        have lem := Kinding.value j2
        exfalso; apply Value.sound lem _ r
  case tlam Γ P t j ih =>
    cases r
    case bind1 i ts' h r =>
      apply Fin.elim0 i
    case bind2 t' r =>
      replace ih := ih r
      apply Typing.tlam ih

theorem preservation : Γ ⊢ t : A -> t ~>* t' -> Γ ⊢ t' : A := by
  intro j r
  induction r
  case _ => exact j
  case _ y z r1 r2 ih =>
    apply preservation_step ih r2

end OneSortHomArityGen
