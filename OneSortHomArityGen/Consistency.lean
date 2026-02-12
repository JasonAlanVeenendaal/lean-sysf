import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding
import OneSortHomArityGen.Typing
import OneSortHomArityGen.Reduction
import OneSortHomArityGen.Progress
import OneSortHomArityGen.Preservation
import OneSortHomArityGen.SN
import OneSortHomArityGen.Model
import OneSortHomArityGen.StrongNorm2

namespace OneSortHomArityGen

open LeanSubst

@[simp]
theorem Ctx.dnth_nil {n : Nat} : (Ctx.nil (T := Term))[n] = ★ := by
  unfold getElem; unfold instGetElemCtxNatTrue; simp

inductive Spine : Term -> Prop where
| var : (n : Nat) -> Spine #n
| cons1 : (Spine f) -> (Spine (f :@ a))
| cons2 : (Spine f) -> (Spine (f :@[a]))

theorem empty_context_untyped : Value t -> Spine t -> ¬(Ctx.nil ⊢ t : T) := by
  intro h1 h2 h3
  induction t generalizing T
  case _ n =>
    cases h3
    case _ h3 h4 => simp at h4; subst h4; cases h3
  case _  n v ts t ih1 ih2 =>
    cases h2
  case _ n v ts ih =>
    cases v
    case _ => cases h3
    case _ =>
      cases h3
      case _ A f a h4 h3 =>
        apply ih 0
        case _ =>
          simp
          cases h1
          case _ h5 h1 => simp at h5; rcases h5 with ⟨e1,e2⟩; apply e1
        case _ =>
          simp
          generalize zdef : f :@ a = z at *
          cases h2
          case _ => injection zdef
          case _ h2 =>
            injection zdef with _ _ e
            simp at e
            cases e
            case _ e1 e2 => subst e1; exact h2
          case _ f' a' h2 => injection zdef with e1 e2 e3; simp at e2
        case _ => simp; apply h3
    case _ =>
      cases h3
      case _ P f a h4 h5 h3 =>
        apply ih 0
        case _ =>
          simp
          cases h1
          case _ h1 h6 =>
            simp at h1
            rcases h1
            case _ e1 e2 =>
              apply e1
        case _ =>
          simp
          generalize zdef : (f :@[a]) = z at *
          cases h2
          case _ => injection zdef
          case _ f' a' h2 => injection zdef with e1 e2 e3; simp at e2
          case _ f' a' h2 => injection zdef with e1 e2 e3; simp at e3; rcases e3 with ⟨e4,e5⟩; subst e4; apply h2
        case _ =>
          simp
          apply h4
    case _ => cases h3

theorem star_context_untyped : Value t -> Spine t -> ¬((★::Ctx.nil) ⊢ t : T) := by
  intro h1 h2 h3
  induction t generalizing T
  case _ n =>
    cases h3
    case _ j1 j2 =>
      cases n
      case _ => simp at j2; subst j2; rcases j1
      case _ => simp at j2; subst j2; rcases j1
  case _ n v ts t ih1 ih2 =>
    rcases h2
  case _ n v ts ih =>
    cases v
    case _ =>
      cases h2
    case _ =>
      cases h3
      case _ A f a h4 h3 =>
        apply ih 0
        case _ =>
          simp
          cases h1
          case _ h5 h6 =>
            simp at h5
            rcases h5 with ⟨e1,e2⟩
            apply e1
        case _ =>
          simp
          generalize zdef : (f :@ a) = z at *
          cases h2
          all_goals try (injection zdef)
          case _ f' a' j1 e1 e2 e3 =>
            simp at e3
            rcases e3 with ⟨e4,e5⟩
            subst e4 e5
            apply j1
          case _ f' a' j1 e1 e2 e3 =>
            simp at e3
            rcases e3 with ⟨e4,e5⟩
            subst e4 e5
            apply j1
        case _ =>
          simp
          apply h3
    case _ =>
      cases h3
      case _ P f a j1 j2 h3 =>
      apply ih 0
      case _ =>
        simp
        cases h1
        case _ j3 j4 =>
          simp at j3
          rcases j3 with ⟨e1,e2⟩
          apply e1
      case _ =>
        simp
        generalize zdef : (f :@[a]) = z at *
        cases h2
        all_goals try (injection zdef)
        case _ f' a' h6 h4 h5 h2 =>
          simp at h2
          rcases h2 with ⟨e1,e2⟩
          subst e1 e2
          apply h6
        case _ f' a' h2 eq1 eq2 eq3 =>
        simp at eq3
        rcases eq3 with ⟨e1,e2⟩
        subst e1 e2
        apply h2
      case _ =>
        simp
        apply j1
    case _ =>
      cases h2

theorem value_decomposition : Value t -> Γ ⊢ t : T -> (∃ A b, t = :λ[A]b ) ∨ (∃ b, t = Λ b) ∨ Spine t := by
  intro h1 h2
  induction h2
  case var Γ' t' n h3 h2 =>
    apply Or.inr
    apply Or.inr
    apply Spine.var
  case app Γ' A B f a j1 j2 ih1 ih2 =>
    cases h1
    case _ h1 h2 =>
      simp at h1
      rcases h1 with ⟨e1,e2⟩
      replace ih1 := ih1 e1
      rcases ih1 with ih1 | ih1 | ih1
      case _ =>
        rcases ih1 with ⟨C, b, ih1⟩
        subst ih1
        simp at h2
      case _ =>
        rcases ih1 with ⟨b, ih1⟩
        subst ih1
        cases j1
      case _ =>
        apply Or.inr
        apply Or.inr
        apply Spine.cons1
        apply ih1
  case _ Γ' A B t' j2 j1 ih =>
    apply Or.inl
    apply Exists.intro A
    apply Exists.intro t'
    simp
  case _ Γ' P P' f a j3 j2 j1 ih =>
    cases h1
    case _ j4 j5 =>
      simp at j4
      rcases j4 with ⟨e1, e2⟩
      replace ih := ih e1
      rcases ih with ih1 | ih1 | ih1
      case _ =>
        rcases ih1 with ⟨e3, e4, e5⟩
        subst e5
        generalize zdef : (:λ[e3] e4) = z at *
        cases j3
        case _ => injection zdef
        case _ => injection zdef
        case _ => injection zdef
        case _ => injection zdef with boo; simp at boo
      case _ =>
        rcases ih1 with ⟨e3, e4⟩
        subst e4
        simp at j5
      case _ =>
        apply Or.inr
        apply Or.inr
        apply Spine.cons2
        apply ih1
  case _ Γ' P t' j1 ih =>
    apply Or.inr
    apply Or.inl
    apply Exists.intro t'
    simp


theorem value_app_spine : Value (f :@ a) -> (Γ ⊢ (f :@ a) : T) -> Spine f := by
  intro h1 h2
  generalize zdef : (f :@ a) = z at *
  induction h1 generalizing f a T
  case _ => simp at zdef
  case _ n v ts j1 j2 ih =>
    cases v
    case _ => injection zdef with e1; simp at e1
    case _ =>
      injection zdef with e1 e2 e3
      clear e1 e2
      subst e3
      simp at j2
      rcases j2 with ⟨e1,e2⟩
      generalize zdef : (f :@ a) = z at *
      cases h2
      all_goals try (injection zdef)
      case _ A' f'' a'' A f' a' j2 j3 =>
        simp at j3
        rcases j3 with ⟨e3,e4⟩
        subst e3 e4
        have lem1 : (∃ A b, f = :λ[A]b ) ∨ (∃ b, f = Λ b) ∨ Spine f := by
          apply value_decomposition
          case _ => apply e1
          case _ => apply f'
        cases lem1
        case _ j3 =>
          rcases j3 with ⟨A, b, hh⟩
          subst hh
          simp at j1
        case _ h =>
          rcases h with ⟨e3,e4⟩
          case _ => subst e4; rcases f'
          case _ h => apply h
      case _ e1 e2 =>
        simp at e1
    case _ => injection zdef with _ e _; injection e
    case _ => injection zdef with e1 e2 e3; simp at e2
  case _ => injection zdef

theorem value_tapp_spine : Value (f :@[A]) -> (Γ ⊢ (f :@[A]) : T) -> Spine f := by
  intro h1 h2
  generalize zdef : (f :@[A]) = z at *
  induction h1 generalizing f A T
  case _ => injection zdef
  case _ n v ts j1 j2 ih =>
    cases v
    all_goals try (injection zdef)
    case _ e1 e2 e3 => simp at e1
    case _ e1 e2 e3 => simp at e2
    case _ e1 e2 e3 =>
      clear e1 e2
      simp at j2
      rcases j2 with ⟨e1,e2⟩
      simp at e3
      cases h2
      case _ P f' a j3 j4 j2 =>
      rcases e3 with ⟨left,right⟩
      simp at left right
      subst left right
      have lem1 : (∃ A b, f = :λ[A]b ) ∨ (∃ b, f = Λ b) ∨ Spine f := by
        apply value_decomposition
        case _ =>
          simp at e1
          apply e1
        case _ =>
          apply j3
      cases lem1
      case _ h =>
        rcases h with ⟨A', b ,three⟩
        subst three
        generalize zdef : (:λ[A']b ) = z at *
        cases j3
        all_goals try (injection zdef)
        case _ f1 f2 f3 f4 => simp at f1
      case _ h =>
        cases h
        case _ h =>
          rcases h with ⟨b, e3⟩
          subst e3
          simp at j1
        case _ h => apply h
    case _ e1 e2 e3 => simp at e2
  case _ => injection zdef


theorem value_consistency : Value t -> ¬(Ctx.nil ⊢ t : :∀ #0) := by
  intro h1
  intro h2
  induction h1
  case _ n =>
    cases h2
    case _ h1 h2 => simp at h2
  case _ n v ts h3 h1 ih =>
    cases h2
    case _ A f a h4 h2 =>
      have lem1 : Ctx.nil ⊢ (f :@ a) : :∀ #0 := by
        apply Typing.app h2
        case _ => apply h4
      have lem2 : Value (f :@ a) := by
        apply Value.ctor
        case _ => apply h3
        case _ => apply h1
      apply empty_context_untyped (t := (f :@ a))
      case _ => apply lem2
      case _ =>
        apply Spine.cons1
        apply value_app_spine
        case _ => apply lem2
        case _ => apply lem1
      case _ => apply lem1
    case _ P f a h5 h4 h2 =>
      have lem1 : Ctx.nil ⊢ (f :@[a]) : :∀ #0 := by
        apply Typing.tapp h5
        case _ => apply h4
        case _ => apply h2
      have lem2 : Value (f :@[a]) := by
        apply Value.ctor
        case _ => apply h3
        case _ => apply h1
      apply empty_context_untyped (t := f :@[a])
      case _ => apply lem2
      case _ =>
        apply Spine.cons2
        apply value_tapp_spine
        case _ => apply lem2
        case _ => apply lem1
      case _=> apply lem1
  case _ ih =>
    cases h2
    case _ t' a h3 h2 h1 =>
      cases h1
      case _ n h1 h4 =>
        cases n
        case _ => simp at h1
        case _ => simp at h1
      case _ A f a' h4 h1 =>
        have lem1 : (★::Ctx.nil) ⊢ (f :@ a') : #0 := by
          apply Typing.app
          case _ => apply h1
          case _ => apply h4
        have lem2 : Spine f := by
          apply value_app_spine
          case _ => apply a
          case _ => apply lem1
        rcases a
        case _ j1 j2 =>
          simp at j1
          rcases j1 with ⟨e1,e2⟩
          apply star_context_untyped
          case _ => apply e1
          case _ => apply lem2
          case _ => apply h1
      case _ P f a' j1 j2 h1 =>
        have lem1 : (★::Ctx.nil) ⊢ (f :@[a']) : #0 := by
          apply Typing.tapp
          case _ => apply j1
          case _ => apply j2
          case _ => apply h1
        have lem2 : Spine f := by
          apply value_tapp_spine
          case _ => apply a
          case _ => apply lem1
        rcases a
        case _ j3 j4 =>
          simp at j3
          case _ =>
            rcases j3 with ⟨e1,e2⟩
            case _ =>
              apply star_context_untyped
              case _ => apply e1
              case _ => apply lem2
              case _ => apply j1

theorem value_irreducible : Normal Red t -> Value t := by
  intro j
  induction t
  case _ n => apply Value.var
  case _ n v ts t ih1 ih2 =>
    apply Value.bind
    case _ =>
      cases v
      case _ =>
        simp
        apply ih1
        intro j1
        apply j
        rcases j1 with ⟨t', j1⟩
        apply Exists.intro (Term.bind Variant.lam v[t'] t)
        apply Red.bind1 .lam 0
        case _ =>
          intro j1
          intro j2
          cases j1 using Fin.cases1
          simp at j2
        case _ => apply j1
      case _ =>
        simp
      case _ =>
        simp
    case _ =>
      apply ih2
      intro j2
      apply j
      rcases j2 with ⟨t',j2⟩
      apply Exists.intro (Term.bind v ts t')
      apply Red.bind2
      apply j2
  case _  n v h ih =>
    cases v
    case _ =>
      apply Value.ctor
      case _ => simp
      case _ => simp
    case _ =>
      apply Value.ctor
      case _ =>
        rw [<-Vec.eta2 h] at *
        generalize zdef : (h 0) = z at *
        cases z
        all_goals try (simp)
        case _ n v ts t =>
          cases v
          case _ =>
            exfalso
            apply j
            apply Exists.intro (t[su (h 1)::+0])
            rw [<-Vec.eta1 ts]
            apply Red.beta
          case _ => simp
          case _ => simp
      case _ =>
        simp
        apply And.intro
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t', j1⟩
          apply j
          rw [<-Vec.eta2 h]
          apply Exists.intro (t' :@ h 1)
          apply Red.ctor .app 0
          case _ => simp
          case _ => simp; apply j1
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t', j1⟩
          apply j
          rw [<-Vec.eta2 h]
          apply Exists.intro (h 0 :@ t')
          apply Red.ctor .app 1
          case _ => simp
          case _ => simp; apply j1
    case _ =>
      apply Value.ctor
      case _ =>
        rw [<-Vec.eta2 h] at *
        generalize zdef : (h 0) = z at *
        cases z
        all_goals try (simp)
        case _ n v ts t =>
          cases v
          case _ =>
            simp
          case _ =>
            exfalso
            apply j
            apply Exists.intro (t[su (h 1)::+0])
            simp
            apply Red.tbeta
          case _ =>
            simp
      case _ =>
        simp
        apply And.intro
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t',j1⟩
          apply j
          rw [<-Vec.eta2 h]
          apply Exists.intro (t' :@[h 1])
          apply Red.ctor .tapp 0
          case _ => simp
          case _ => simp; apply j1
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t',j1⟩
          apply j
          rw [<-Vec.eta2 h]
          apply Exists.intro (h 0 :@[t'])
          apply Red.ctor .tapp 1
          case _ => simp
          case _ => simp; apply j1
    case _ =>
      apply Value.ctor
      case _ => simp
      case _ =>
        simp
        apply And.intro
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t',j1⟩
          apply j
          apply Exists.intro (Term.ctor Variant.arr v[t', h 1])
          apply Red.ctor .arr 0
          case _ =>
            simp
          case _ =>
            apply j1
        case _ =>
          apply ih
          intro j1
          rcases j1 with ⟨t',j1⟩
          apply j
          apply Exists.intro (Term.ctor Variant.arr v[h 0, t'])
          apply Red.ctor .arr 1
          case _ =>
            simp
          case _ => apply j1

theorem strong_weak : SN Red t -> WN Red t := by
  intro j
  induction j
  case _ x j ih =>
    have lem := progress x
    cases lem
    case _ h =>
      apply Exists.intro x
      apply And.intro
      apply Star.refl
      simp [Normal, Reducible]
      apply Value.sound h
    case _ h =>
      rcases h with ⟨y,h⟩
      replace ih := ih y h
      rcases ih with ⟨t,ih⟩
      rcases ih with ⟨left,right⟩
      apply Exists.intro t
      simp [NormalForm]
      apply And.intro
      case _ =>
        have lem : x ~>* x := by
          apply Star.refl
        have lem2 : x ~>* y := by
          apply Star.step lem h
        apply Star.trans
        case _ => apply lem2
        case _ => apply left
      case _ => apply right

theorem value_step : Γ ⊢ t : T -> Value t ∨ (∃ t' , t ~>* t' ∧ Value t') := by
  intro j
  have lem2 : SN Red t := by
    apply Normalization.Version2.strong_normalization
    case _ => apply j
  replace lem2 := strong_weak lem2
  rcases lem2 with ⟨t',lem2⟩
  rcases lem2 with ⟨e1,e2⟩
  replace e2 := value_irreducible e2
  apply Or.inr
  apply Exists.intro t'
  apply And.intro
  case _ => apply e1
  case _ => apply e2


theorem consistency : ¬ (Ctx.nil ⊢ t : :∀ #0) := by
  intro j
  have lem1 : Value t ∨ (∃ t', t ~>* t' ∧ Value t') := by
    apply value_step
    case _ => apply j
  cases lem1
  case _ h =>
    apply value_consistency
    case _ => apply h
    case _ => apply j
  case _ h =>
    rcases h with ⟨t', h⟩
    rcases h with ⟨h1,h2⟩
    apply value_consistency
    case _ => apply h2
    case _ =>
      apply preservation
      case _ => apply j
      case _ => apply h1

end OneSortHomArityGen
