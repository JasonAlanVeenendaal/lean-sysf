import LeanSubst
import TwoSortHet.Term

namespace TwoSortHet

open LeanSubst

universe u u1 u2 u3

class Model (D : Sort u) where
  A : D -> D -> D
  Q : (D -> D) -> D

@[simp]
def ModelCons : D -> (Nat -> D) -> (Nat -> D)
| d, _, 0 => d
| _, v, n + 1 => v n

@[simp]
def Model.int_ty [Model D] (v : Nat -> D) : Ty -> D
| t#x => v x
| .arrow B C => A (int_ty v B) (int_ty v C)
| .all _ t => Q (λ d => int_ty (ModelCons d v) t)

@[simp]
def Model.int_subst [Model D] (v : Nat -> D) (σ : Subst Ty) : Nat -> D
| i => Model.int_ty v (σ.act i)

notation "⟦ " t " ⟧ " v:100 => Model.int_ty v t
notation "⟦ " σ " ⟧ " v:100 => Model.int_subst v σ
notation d "::" v:100 => ModelCons d v

@[simp]
theorem Model.rename [Model D] {A : Ty} {ξ : Nat -> D} (r : Ren)
  : ⟦ A[r] ⟧ ξ = ⟦ A ⟧ (ξ ∘ r.act)
:= by
  induction A generalizing ξ r
  case _ n =>
    simp
    generalize zdef : r.act n = z
    let lem : Ty.from_action ((r.to).act n) = t#z := by
      simp [Ren.to]
      apply zdef
    rw [lem]
    simp
  case _ ih =>
    simp
    congr
    funext d
    replace ih := @ih (d::ξ) r.lift
    simp at ih
    rw [Ren.to_lift] at ih
    simp at ih
    rw [ih]
    congr
    funext x
    cases x
    case _ =>
      simp [Ren.lift]
    case _ =>
      simp [Ren.lift]
  case _ ih1 ih2 =>
    simp
    rw [ih1]
    rw [ih2]


@[simp]
theorem Model.weaken [Model D] {A : Ty} {ξ : Nat -> D}
  : ⟦ A[+1] ⟧ (d :: ξ) = ⟦ A ⟧ ξ
:= by
  have lem := Model.rename (A := A) (ξ := d::ξ) (Ren.mk (· + 1))
  have lem2 : Ren.to (Ren.mk (· + 1)) = @Subst.succ Ty := by
    congr
    funext
  rw [<-lem2]
  rw [lem]
  simp
  have lem : ((d::ξ) ∘ (· + 1)) = ξ := by
    funext n
    cases n
    case _ =>
      simp
    case _ =>
      simp
  rw [lem]

@[simp]
theorem Model.subst [Model D] {A : Ty} {σ : Subst Ty} {ξ : Nat -> D}
  : ⟦ A[σ] ⟧ ξ = ⟦ A ⟧ (⟦ σ ⟧ ξ)
:= by
  induction A generalizing σ ξ
  case _ =>
    simp
  case _ ih =>
    simp
    congr
    funext
    rw [ih]
    congr
    funext i
    cases i
    case _ =>
      simp [Subst.compose]
    case _ n =>
      simp [Subst.compose]
      generalize σ.act n = z
      cases z
      case _ =>
        simp
      case _ =>
        simp
  case _ ih1 ih2 =>
    simp
    rw [ih1]
    rw [ih2]
