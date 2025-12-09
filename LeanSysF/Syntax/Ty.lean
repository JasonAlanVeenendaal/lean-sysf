
import LeanSubst
import LeanSysF.Syntax.Syntax

open LeanSubst

-- Technically star is a kind, but it will serve a purpose
-- and also not get in the way so we include it here
inductive IsTy : Syntax -> Prop
| star : IsTy .star
| var n : IsTy (.var n)
| arr : IsTy A -> IsTy B -> IsTy (.ctor2 .arr A B)
| all : IsTy P -> IsTy (.bind1 .all P)

abbrev Ty := {t:Syntax // IsTy t}

namespace Ty

  def star : Ty := .mk .star .star

  notation "★" => star

  def var (n : Nat) : Ty := .mk (.var n) (.var n)

  def arr : Ty -> Ty -> Ty
  | .mk A pA, .mk B pB => .mk (.ctor2 .arr A B) (.arr pA pB)

  notation A "-t>" B => arr A B

  def all : Ty -> Ty
  | .mk P pP => .mk (.bind1 .all P) (.all pP)

  notation ":∀ " P => all P

  @[simp]
  def inj : Syntax -> Ty
  | .star => .star
  | .var n => .var n
  | .ctor2 .arr A B => .arr (inj A) (inj B)
  | .bind1 .all P => .all (inj P)
  | _ => .var 0

  theorem inj_stable : (p : IsTy t) -> (inj t) = ⟨t, p⟩ := by
    intro p; induction t
    all_goals try cases p
    case _ => simp [inj, star]
    case _ => simp [inj, var]
    case _ => simp [inj, all, *]
    case _ => simp [inj, arr, *]

  instance inst1 : SubtypeInject IsTy where
    inj := inj
    inj_stable := inj_stable

  theorem closed : ∀ lf f t, IsTy t ->
    IsTy (SubstMap.smap
      (Subtype.lift IsTy lf)
      (Subtype.prj IsTy f)
      t)
  := by
    intro lf f t h
    induction h generalizing f
    all_goals simp [SubstMap.smap]
    case star => apply IsTy.star
    case var x =>
      generalize zdef : f x = z
      cases z <;> simp at *
      case _ => apply IsTy.var
      case _ t =>
        cases t; case _ t tp =>
        simp [*]
    case arr ih1 ih2 =>
      apply IsTy.arr
      apply ih1 f
      apply ih2 f
    case all ih =>
      apply IsTy.all
      apply ih (lf (Subtype.inj IsTy (Subtype.prj IsTy f)))

  instance inst2 : Subtype.SubstMapClosed IsTy where
    closed := closed

  theorem lift_eq_lemma : Subtype.prj IsTy (Subst.lift σ) = #0::Subtype.prj IsTy σ ∘ S := by
    funext; case _ x =>
    cases x <;> simp [Subst.lift]
    case _ x =>
      generalize zdef : σ x = z
      cases z <;> simp
      case _ => simp [Subst.compose, *]
      case _ t =>
        cases t; case _ t p =>
        simp [Subst.compose, *]
        rw [apply_stable (r := (· + 1)) (σ := S) rfl]

  theorem lift_eq : ∀ σ t,
    smap (Subtype.lift IsTy Subst.lift) (Subtype.prj IsTy σ) t
      = smap Subst.lift (Subtype.prj IsTy σ) t
  := by
    intro σ t
    induction t generalizing σ <;> simp [*, -smap_to_notation] at *
    case lam ih1 ih2 =>
      have lem1 := Subtype.prj_inj IsTy; simp at lem1
      replace ih2 := ih2 (Subst.lift σ)
      rw [lem1 σ, <-lift_eq_lemma]
    case bind1 ih =>
      have lem1 := Subtype.prj_inj IsTy; simp at lem1
      replace ih := ih (Subst.lift σ)
      rw [lem1 σ, <-lift_eq_lemma]

  instance : Subtype.SubstMapLift IsTy where
    lift_eq := lift_eq

  @[simp, coe]
  def action_coe : Subst.Action Ty -> Ty
  | .re y => var y
  | .su t => t

  instance : Coe (Subst.Action Ty) Ty where
    coe := action_coe

  @[simp]
  theorem subst_star : ★[σ] = ★ := by simp [star]

  @[simp]
  theorem subst_var : (var x)[σ] = σ x := by
    simp [var]
    split <;> simp [*]

  @[simp]
  theorem subst_arr : (A -t> B)[σ] = A[σ] -t> B[σ] := by
    simp [arr, Subst.apply]
    sorry

  @[simp]
  theorem subst_all : (:∀ P)[σ] = :∀ P[σ.lift] := by
    sorry

end Ty
