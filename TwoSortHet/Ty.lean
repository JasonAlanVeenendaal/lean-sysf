
import LeanSubst

namespace TwoSortHet

open LeanSubst

inductive Ty : Type where
| var : Nat -> Ty
| arr : Ty -> Ty -> Ty
| all : Ty -> Ty

prefix:max "!#" => Ty.var
notation:64 A:63 " -:> " B:64 => Ty.arr A B
notation ":∀ " t => Ty.all t

@[simp]
instance : Inhabited Ty where
  default := !#0

@[coe]
def Ty.from_action : Subst.Action Ty -> Ty
| .re y => !#y
| .su t => t

@[simp]
theorem Ty.from_action_id {n} : from_action (+0 n) = !#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Ty.from_action_succ {n} : from_action (+1 n) = !#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Ty.from_acton_re {n} : from_action (re n) = !#n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (lf : Endo Ren) (r : Ren) : Ty -> Ty
| !#x => !#(r x)
| A -:> B => rmap lf r A -:> rmap lf r B
| :∀ P => :∀ rmap lf (lf r) P

instance : RenMap Ty where
  rmap := Ty.rmap

@[simp]
def Ty.smap (lf : Endo (Subst Ty)) (σ : Subst Ty) : Ty -> Ty
| !#x => σ x
| A -:> B => smap lf σ A -:> smap lf σ B
| :∀ P => :∀ smap lf (lf σ) P

instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
theorem Ty.subst_var : (!#x)[σ:Ty] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_arr : (A -:> B)[σ:Ty] = A[σ:_] -:> B[σ:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.subst_all : (:∀ P)[σ:Ty] = :∀ P[σ.lift:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_compose {x} {σ τ : Subst Ty}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Ty.from_action]

theorem Ty.apply_id {t : Ty} : t[+0] = t := by subst_solve_id Ty, Ty, t

instance : SubstMapId Ty Ty where
  apply_id := Ty.apply_id

theorem Ty.apply_stable (r : Ren) (σ : Subst Ty)
  : r.to = σ -> Ren.apply (T := Ty) r = Subst.apply σ
:= by subst_solve_stable Ty, r, σ

instance : SubstMapStable Ty where
  apply_stable := Ty.apply_stable

theorem Ty.apply_compose {s : Ty} {σ τ : Subst Ty} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Ty, s, σ, τ

instance : SubstMapCompose Ty Ty where
  apply_compose := Ty.apply_compose

end TwoSortHet
