
import LeanSubst
import LeanSysF.Utility
import LeanSysF.Term

open LeanSubst

inductive FV : Term -> Nat -> Prop
| var : FV #x x
| ctor {i : Fin v.arity} {ts : Fin v.arity -> Term} : FV (ts i) x -> FV (.ctor v ts) x
| bind1 {i : Fin v.arity} {ts : Fin v.arity -> Term} : FV (ts i) x -> FV (.bind v ts t) x
| bind2 : FV t (x + 1) -> FV (.bind v ts t) x

instance : Membership Nat Term where
  mem := FV

theorem FV.found : x ∈ #x := by simp [Membership.mem]; apply FV.var

@[simp]
theorem FV.ctor_inj : x ∈ (Term.ctor v ts) <-> ∃ i, x ∈ (ts i) := by
  apply Iff.intro
  case _ =>
    intro h; simp [Membership.mem] at *
    cases h; case _ i h =>
    exists i
  case _ =>
    intro h; simp [Membership.mem] at *
    cases h; case _ i h =>
    apply FV.ctor h

@[simp]
theorem FV.bind_inj : x ∈ (Term.bind v ts t) <-> (∃ i, x ∈ (ts i)) ∨ x + 1 ∈ t := by
  apply Iff.intro
  case _ =>
    intro h; cases h
    case _ i h => apply Or.inl; exists i
    case _ h => apply Or.inr; apply h
  case _ =>
    intro h; cases h
    case _ h =>
      cases h; case _ i h =>
      apply FV.bind1 h
    case _ h => apply FV.bind2 h

theorem lift_iterated_succ_is_re
  : ((Subst.lift (T := Term))^[n]) +1 y = z -> ∃ i, z = re i
:= by
  intro h
  induction n generalizing y z
  case zero =>
    simp at h; cases z
    case _ i =>
      injection h with e; subst e
      exists (y + 1)
    case _ t => injection h
  case succ n ih =>
    simp at h
    cases y <;> simp at h
    case zero => exists 0; subst h; rfl
    case succ y =>
      unfold Subst.compose at h; simp at h
      generalize udef : ((Subst.lift (T := Term))^[n]) +1 y = u at *
      cases u <;> simp at *
      case _ i => exists (i + 1); subst h; rfl
      case _ t =>
        replace ih := @ih y; cases ih; case _ i ih =>
        rw [ih] at udef; injection udef

theorem FV.var_not_in_one_more {t : Term} : ¬ (x ∈ t[((Subst.lift)^[x]) +1]) := by
  intro h
  induction t generalizing x <;> simp at *
  case var y =>
    induction x generalizing y <;> simp at *
    case _ => cases h
    case _ n ih =>
      cases y <;> simp at *
      case _ => cases h
      case _ y =>
        unfold Subst.compose at h; simp at h
        generalize zdef : (((Subst.lift (T := Term))^[n]) +1 y) = z at *
        cases z <;> simp at *
        case _ z =>
          replace ih := ih y
          cases h; rw [zdef] at ih; simp at ih
          apply ih; apply FV.var
        case _ t =>
          have lem := lift_iterated_succ_is_re zdef
          cases lem; case _ i lem =>
          injection lem
  case bind v ts t ih1 ih2 =>
    cases h
    case _ h =>
      cases h; case _ i h =>
      replace ih1 := @ih1 i x
      apply ih1 h
    case _ h =>
      replace ih2 := @ih2 (x + 1); simp at ih2
      apply ih2 h
  case ctor v ts ih =>
    cases h; case _ i h =>
    apply ih i h

theorem FV.zero_not_in_succ {t : Term} : ¬ (0 ∈ t[+1]) := by
  intro j
  have lem := @var_not_in_one_more 0 t; simp at lem
  apply lem j
