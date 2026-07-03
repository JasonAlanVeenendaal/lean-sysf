
import TwoSortHet.Typing
import TwoSortHet.Kinding.Rename
open LeanSubst

namespace TwoSortHet

structure KindingSubst (σ : Subst Ty) (Δ1 Δ2 : List Kind) where
  act : ∀ {x T}, Δ1[x]? = some T -> Δ2 ⊢ₖ σ.act x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => KindingSubst σ Γ Δ

theorem KindingSubst.id Δ : Δ -[+0]> Δ := KindingSubst.mk λ h => .var h

theorem KindingSubst.re (j : Δ2[y]? = some A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[re y::σ]> Δ2 := KindingSubst.mk λ h => sorry

theorem KindingSubst.su (j : Δ2 ⊢ₖ a : A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[su a::σ]> Δ2 := sorry

theorem KindingSubst.lift A :
  Δ1 -[σ]> Δ2 ->
  A::Δ1 -[σ.lift]> A::Δ2
:= sorry

theorem KindingSubst.succ A : Δ -[+1]> A::Δ := sorry

theorem KindingSubst.comp : A -[σ]> B -> B -[τ]> C -> A -[σ ∘ τ]> C := sorry

theorem KindingRen.to (m : A -⟨r⟩> B) : A -[r.to]> B := sorry

theorem Kinding.subst (m : Δ1 -[σ]> Δ2) : Δ1 ⊢ₖ A : K -> Δ2 ⊢ₖ A[σ] : K
| var h => m.act h
-- | lam j => lam (j.subst $ m.lift _)
-- | app j1 j2 => app (j1.subst m) (j2.subst m)
| all j => all (j.subst $ m.lift _)
| arrow j1 j2 => arrow (j1.subst m) (j2.subst m)

theorem Kinding.beta : (A::Δ) ⊢ₖ b : B -> Δ ⊢ₖ t : A -> Δ ⊢ₖ b[su t::+0] : B
| j1, j2 => subst (.su j2 $ .id _) j1

-- theorem Kinding.preservation_step : Δ ⊢ₖ A : K -> A ~t> A' -> Δ ⊢ₖ A' : K
-- | .lam (A := A) h1, .lam_congr j1 => .lam (Kinding.preservation_step h1 j1)
-- | .app h1 h2, .app_congr1 j1 => .app (Kinding.preservation_step h1 j1) h2
-- | .app h1 h2, .app_congr2 j1 => .app h1 (Kinding.preservation_step h2 j1)
-- | .all h1, .all_congr j1 => .all (Kinding.preservation_step h1 j1)
-- | .arrow h1 h2, .arrow_congr1 j1 => .arrow (Kinding.preservation_step h1 j1) h2
-- | .arrow h1 h2, .arrow_congr2 j1 => .arrow h1 (Kinding.preservation_step h2 j1)
-- | .app (.lam h1) h2, .beta => Kinding.beta h1 h2

-- theorem regularity : Δ&Γ ⊢ t : A -> Δ ⊢ₖ A : ★
-- | .var h1 h2 => h2
-- | .lam h1 h2 =>
--   .arrow h1 (regularity h2)
-- | .app h1 h2 =>
--   let lem := regularity h1
--   match lem with
--   |.arrow j1 j2 => j2
-- | .tlam h1 =>
--   let lem := regularity h1
--   .all lem
-- | .tapp h1 h2 h3 =>
--   let lem := regularity h1
--   match lem with
--   | .all j1 => Kinding.beta j1 h2 |> cast (by rw [h3])
-- | .conv (A := A) (B := B) h1 h2 h3 => h3

end TwoSortHet
