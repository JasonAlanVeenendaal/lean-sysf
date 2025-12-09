
import LeanSubst

inductive Ctor2Kind where
| app | tapp | arr

inductive Bind1Kind where
| tlam | all

inductive Syntax where
| star : Syntax
| var : Nat -> Syntax
| lam : Syntax -> Syntax -> Syntax
| bind1 : Bind1Kind -> Syntax -> Syntax
| ctor2 : Ctor2Kind -> Syntax -> Syntax -> Syntax

open LeanSubst

namespace Syntax
  @[simp, coe]
  def action_coe : Subst.Action Syntax -> Syntax
  | .re y => .var y
  | .su t => t

  instance : Coe (Subst.Action Syntax) Syntax where
    coe := action_coe
end Syntax

@[simp]
def smap (lf : Subst.Lift Syntax) (f : Nat -> Subst.Action Syntax) : Syntax -> Syntax
| .star => .star
| .var x => f x
| .lam A t => .lam (smap lf f A) (smap lf (lf f) t)
| .bind1 k t => .bind1 k (smap lf (lf f) t)
| .ctor2 k t1 t2 => .ctor2 k (smap lf f t1) (smap lf f t2)

instance SubstMap_Term : SubstMap Syntax where
  smap := smap

@[simp]
theorem smap_to_notation : smap Subst.lift σ t = t[σ] := by
  unfold Subst.apply
  unfold SubstMap.smap
  unfold SubstMap_Term
  simp

@[simp]
theorem subst_star : Syntax.star[σ] = .star := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_var : (Syntax.var x)[σ] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_lam : (Syntax.lam A t)[σ] = Syntax.lam A[σ] t[σ.lift] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_bind1 : (Syntax.bind1 k t)[σ] = .bind1 k (t[σ.lift]) := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_ctor2 : (Syntax.ctor2 k t1 t2)[σ] = .ctor2 k (t1[σ]) (t2[σ]) := by
  unfold Subst.apply; simp [SubstMap.smap]

theorem apply_id {t : Syntax} : t[I] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

theorem apply_stable {r : Ren} {σ : Subst Syntax}
  : r.to = σ -> Ren.apply r = Subst.apply σ
:= by solve_stable r, σ

instance SubstMapStable_Syntax : SubstMapStable Syntax where
  apply_id := apply_id
  apply_stable := apply_stable

theorem apply_compose {s : Syntax} {σ τ : Subst Syntax} : s[σ][τ] = s[σ ∘ τ] := by
  solve_compose Syntax, s, σ, τ

instance SubstMapCompose_Syntax : SubstMapCompose Syntax where
  apply_compose := apply_compose
