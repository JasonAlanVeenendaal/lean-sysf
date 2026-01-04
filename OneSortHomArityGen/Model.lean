
import LeanSubst
import OneSortHomArityGen.Term

namespace OneSortHomArityGen

open LeanSubst

universe u u1 u2 u3

class Model (D : Sort u) where
  A : D -> D -> D
  Q : (D -> D) -> D
  P : D -- Any model has to know what to do with junk

@[simp]
def Model.int_term [Model D] (v : Nat -> D) : Term -> D
| #x => v x
| .ctor .arr ts => A (int_term v (ts 0)) (int_term v (ts 1))
| .bind .all _ t => Q (λ d => int_term (d::v) t)
| _ => P

@[simp]
def Model.int_subst [Model D] (v : Nat -> D) (σ : Subst Term) : Nat -> D
| i => Model.int_term v (σ i)

notation "⟦ " t " ⟧ " v:100 => Model.int_term v t
notation "⟦ " σ " ⟧ " v:100 => Model.int_subst v σ

theorem Model.rename [Model D] {A : Term} {ξ : Nat -> D} (r : Ren)
  : ⟦ A[r] ⟧ ξ = ⟦ A ⟧ (ξ ∘ r)
:= by
  induction A generalizing r ξ <;> simp at *
  case ctor v _ ih =>
    cases v <;> simp at *; case _ ts =>
    generalize Adef : ts 0 = A at *
    generalize Bdef : ts 1 = B at *
    rcases ih with ⟨ih1, ih2⟩; congr 1
    rw [ih1]; rw [ih2]
  case bind v _ _ ih1 ih2 =>
    cases v <;> simp at *
    congr; funext; case _ d =>
    replace ih2 := @ih2 (d::ξ) r.lift
    rw [Ren.to_lift (S := Term)] at ih2
    simp at ih2; rw [ih2]; congr
    funext; case _ i =>
    cases i <;> simp [Ren.lift]

@[simp]
theorem Model.weaken [Model D] {A : Term} {ξ : Nat -> D}
  : ⟦ A[+1] ⟧ (d::ξ) = ⟦ A ⟧ ξ
:= by
  have lem := Model.rename (A := A) (ξ := d::ξ) (· + 1)
  simp at lem; rw [lem]
  have lem : ((d::ξ) ∘ (· + 1)) = ξ := by
    funext; case _ i =>
    cases i <;> simp
  rw [lem]

theorem Model.subst [Model D] {A : Term} {σ : Subst Term} {ξ : Nat -> D}
  : ⟦ A[σ] ⟧ ξ = ⟦ A ⟧ (⟦ σ ⟧ ξ)
:= by
  induction A generalizing σ ξ <;> simp
  case ctor v _ ih =>
    cases v <;> simp
    simp [*]
  case bind v _ _ ih1 ih2 =>
    cases v <;> simp
    congr; funext; case _ d =>
    replace ih2 := @ih2 σ.lift (d::ξ)
    simp at ih2; rw [ih2]; congr
    funext; case _ i =>
    cases i <;> simp [Subst.compose]
    case _ i =>
    generalize σ i = z
    cases z <;> simp

@[simp]
theorem Model.beta [Model D] {A B : Term} {ξ : Nat -> D}
  : ⟦ A[su B::+0] ⟧ ξ = ⟦ A ⟧ (⟦ B ⟧ ξ :: ξ)
:= by
  rw [Model.subst]; congr
  funext; case _ i =>
  cases i <;> simp

end OneSortHomArityGen
