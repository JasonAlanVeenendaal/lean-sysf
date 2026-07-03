
import TwoSortHet.Typing
import TwoSortHet.Typing.Rename
import TwoSortHet.Kinding.Substitute
open LeanSubst

namespace TwoSortHet

structure TypingSubst (σ : Subst Term) (Δ : List Kind) (Γ1 Γ2 : List Ty) where
  act : ∀ {x T}, Γ1[x]? = some T -> Δ&Γ2 ⊢ σ.act x : T

notation:1000 Δ:1000 " ⊢ₛ " Γ1:1000 " -[" σ "]> " Γ2:1000 => TypingSubst σ Δ Γ1 Γ2

theorem TypingSubst.id : Δ ⊢ₛ X -[+0]> X := .mk @λ x T h => Typing.var h sorry

theorem TypingSubst.re (j : Γ2[y]? = some A) (m : Δ ⊢ₛ Γ1 -[σ]> Γ2)
  : Δ ⊢ₛ (A::Γ1) -[re y::σ]> Γ2 := .mk @λ x T h =>
    match x with
    | 0 => Typing.var (j |> cast (by simp at h; subst h; rfl)) sorry
    | n + 1 =>
      have lem := m.act h
      lem

theorem TypingSubst.su (j : Δ&Γ2 ⊢ a : A) (m : Δ ⊢ₛ Γ1 -[σ]> Γ2)
  : Δ ⊢ₛ (A::Γ1) -[su a::σ]> Γ2 := .mk @λ x T h =>
    match x with
    | 0 => by simp at *; subst h; apply j
    | n+ 1 =>
      have lem := m.act h
      lem

theorem TypingSubst.lift {Γ1 Γ2 : List Ty} A
  : Δ ⊢ₛ Γ1 -[σ]> Γ2 -> Δ ⊢ₛ (A::Γ1) -[σ.lift]> (A::Γ2)
| j => .mk @λ x T h =>
  match x with
  | 0 => Typing.var h sorry
  | n + 1 =>
    have lem := j.act h
    sorry

theorem TypingSubst.comp : Δ ⊢ₛ A -[σ]> B -> Δ ⊢ₛ B -[τ]> C -> Δ ⊢ₛ A -[σ ∘ τ]> C := sorry

theorem TypingSubst.hcomp :
  Δ1 ⊢ₛ A -[σ]> B ->
  Δ1 -[τ]> Δ2 ->
  Δ2 ⊢ₛ A[τ:Ty] -[σ ◾ τ]> B[τ:Ty]
:= sorry

theorem Typing.subst (m : Δ ⊢ₛ Γ1 -[σ]> Γ2) : Δ&Γ1 ⊢ t : A -> Δ&Γ2 ⊢ t[σ] : A
| var h j => m.act h
| lam j1 j2 => lam j1 (j2.subst $ m.lift _)
| app j1 j2 => app (j1.subst m) (j2.subst m)
| tlam (K := K) j =>
  have m' : (K::Δ) ⊢ₛ Γ1⟨Ren.add 1⟩ -[σ ◾ +1@Ty]> Γ2⟨Ren.add 1⟩ := sorry
  tlam (j.subst m')
| tapp j1 j2 e => tapp (j1.subst m) j2 e
--| conv j1 cv j2 => sorry

theorem Typing.beta : Δ&(A::Γ) ⊢ b : B -> Δ&Γ ⊢ t : A -> Δ&Γ ⊢ b[su t::+0] : B
| j1, j2 => j1.subst $ .su j2 .id

end TwoSortHet
