import LeanSubst
import TwoSortHet.Typing
import TwoSortHet.Kinding.Substitute
open LeanSubst

namespace TwoSortHet

-- inductive Neutral : Ty -> Prop where
-- | var : Neutral (.var x)
-- | app : Neutral f -> Neutral (f • a)

-- inductive Value : Ty -> Prop where
-- | var : Value (.var x)
-- | arrow : Value A -> Value B -> Value (A -:> B)
-- | lam : Value t -> Value (λ[K] t)
-- | all : Value t -> Value (∀[K] t)
-- | app : Neutral f -> Value f -> Value a -> Value (f • a)

-- theorem var_step : t#x ~t> A -> ∃ y, A = t#y
-- | j1 => by cases j1

-- theorem var_star_step : t#x ~t>* A -> ∃ y, A = t#y
-- | .refl => ⟨x, rfl⟩
-- | .step h1 h2 =>
--   let ⟨y', e1⟩ := var_star_step h1
--   by
--     rw [e1] at h2
--     replace h2 := var_step h2
--     apply h2

-- theorem app_neutral_step : Neutral f -> f ~t> y -> Neutral y
-- | .app h1, .app_congr1 j1 => .app (app_neutral_step h1 j1)
-- | .app h1, .app_congr2 j1 => .app h1

-- theorem app_neutral_star_step : Neutral f -> f ~t>* y -> Neutral y
-- | j1, .refl => j1
-- | j1, .step h1 h2 => app_neutral_step (app_neutral_star_step j1 h1) h2

-- --need confluence
-- theorem Typing.unique : Δ&Γ ⊢ t : A -> Δ&Γ ⊢ t : A' -> A =t= A'
-- | .var h1 h2, .var j1 j2 => by rw [h1] at j1; injection j1 with w; subst w; apply Conv.refl
-- | .var h1 h2, .conv j1 j2 j3 =>
--   let lem := Typing.unique (.var h1 h2) j1
--   sorry
-- | .lam h1 h2, .lam j1 j2 =>
--   sorry
-- | .lam h1 h2, .conv j1 j2 j3 =>
--   let lem := Typing.unique (.lam h1 h2) j1
--   sorry
-- | .app h1 h2, .app j1 j2 => sorry
-- | .app h1 h2, .conv j1 j2 j3 =>
--   let lem := Typing.unique (.app h1 h2) j1
--   sorry
-- | .tlam h1, .tlam j1 => sorry
-- | .tlam h1, .conv j1 j2 j3 =>
--   let lem := Typing.unique (.tlam h1) j1
--   sorry
-- | .tapp h1 h2 h3, .tapp j1 j2 j3 => sorry
-- | .tapp h1 h2 h3, .conv j1 j2 j3 =>
--   let lem := Typing.unique (.tapp h1 h2 h3) j1
--   sorry
-- | .conv h1 h2 h3, .var j1 j2 =>
--   --let lem := Typing.unique h1 j1
--   sorry
-- | .conv h1 h2 h3, .lam j1 j2 => sorry
-- | .conv h1 h2 h3, .app j1 j2 => sorry
-- | .conv h1 h2 h3, .tlam j1 => sorry
-- | .conv h1 h2 h3, .tapp j1 j2 j3 =>
--   --let lem := Typing.unique h1 (.tapp j1 j2 j3)
--   sorry
-- | .conv h1 h2 h3, .conv j1 j2 j3 =>
--   let lem := Typing.unique h1 j1
--   sorry

end TwoSortHet
