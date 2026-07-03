
import LeanSubst
import TwoSortHet.Term
import TwoSortHet.Reduction
open LeanSubst

namespace TwoSortHet

inductive Kinding : List Kind -> Ty -> Kind -> Prop where
| var :
  Δ[x]? = some K ->
  Kinding Δ t#x K
-- | lam :
--   Kinding (A::Δ) t B ->
--   Kinding Δ (λ[A] t) (A -:> B)
-- | app :
--   Kinding Δ f (A -:> B) ->
--   Kinding Δ a A ->
--   Kinding Δ (f • a) B
| all :
  Kinding (K::Δ) P ★ ->
  Kinding Δ (∀[K] P) ★
| arrow :
  Kinding Δ A ★ ->
  Kinding Δ B ★ ->
  Kinding Δ (A -:> B) ★

notation:170 Δ:170 " ⊢ₖ " A:170 " : " K:170 => Kinding Δ A K

inductive Typing : List Kind -> List Ty -> Term -> Ty -> Prop where
| var :
  Γ[x]? = some T ->
  Δ ⊢ₖ T : ★ ->
  Typing Δ Γ #x T
| lam :
  Δ ⊢ₖ A : ★ ->
  Typing Δ (A::Γ) t B ->
  Typing Δ Γ (λ[A] t) (A -:> B)
| app :
  Typing Δ Γ f (A -:> B) ->
  Typing Δ Γ a A ->
  Typing Δ Γ (f • a) B
| tlam :
  Typing (K::Δ) Γ⟨.add 1⟩ t P ->
  Typing Δ Γ (Λ[K] t) (∀[K] P)
| tapp :
  Typing Δ Γ f (∀[K] P) ->
  Δ ⊢ₖ a : K ->
  P' = P[su a::+0] ->
  Typing Δ Γ (f •[a]) P'
-- | conv :
--   Typing Δ Γ t A ->
--   A =t= B ->
--   Δ ⊢ₖ B : ★ ->
--   Typing Δ Γ t B

notation:170 Δ:170 "&" Γ:170 " ⊢ " t:170 " : " A:170 => Typing Δ Γ t A

-- theorem Typing.type_preservation : Δ&Γ ⊢ t : A -> Δ ⊢ₖ A' : ★ -> A ~t> A' -> Δ&Γ ⊢ t : A'
-- | h1, j1, j2 => .conv h1 (.backward .refl j2) j1

-- theorem test : A =t= A' -> (A -:> B) =t= (A' -:> B)
-- | .refl => .refl
-- | .forward h1 h2 =>
--   let lem := test (B := B) h1
--   let lem2 := Ty.Red.arrow_congr1 (B := B) h2
--   let lem3 := Conv.forward lem lem2
--   lem3
-- | .backward h1 h2 =>
--   let lem := test (B := B) h1
--   let lem2 := Ty.Red.arrow_congr1 (B := B) h2
--   Conv.backward lem lem2

-- -- | .refl, j1 => j1
-- -- | .backward (y := A'') h1 h2, j1 =>
-- --   let lem := Ty.Red.arrow_congr1 (B := B) h2
-- --   have lem2 : Δ&Γ ⊢ t : (A'' -:> B) := type_preservation j1 sorry lem
-- --   .arrow_congr1 h1 lem2
-- -- | .forward (x := A'') h1 h2, j1 =>
-- --   let lem := Ty.Red.arrow_congr1 (B := B) h2
-- --   sorry

-- theorem Typing.arrow_congr2 : B =t= B' -> Δ&Γ ⊢ t : (A -:> B') -> Δ&Γ ⊢ t : (A -:> B') := sorry

-- theorem Kinding.unique : Δ ⊢ₖ A : K -> Δ ⊢ₖ A : K' -> K = K'
-- | .var h1, .var j1 => by rw [h1] at j1; injection j1
-- | .lam h1, .lam j1 =>
--   let lem := Kinding.unique h1 j1
--   by rw [lem]
-- | .app h1 h2, .app j1 j2 =>
--   let lem1 := Kinding.unique h1 j1
--   let lem2 := Kinding.unique h2 j2
--   by rw [lem2] at h1; injection lem1
-- | .all h1, .all j1 => rfl
-- | .arrow h1 h2, .arrow j1 j2 => rfl

end TwoSortHet
