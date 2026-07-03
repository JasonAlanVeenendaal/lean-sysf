
import LeanSubst
import TwoSortHet.Typing
import TwoSortHet.Kinding.Substitute
open LeanSubst

namespace TwoSortHet

def KSet := List Kind -> Ty -> Kind -> Prop
def KSet.empty : KSet := λ _ _ _ => False
def KRed := List Kind -> Ty -> Ty -> Prop

def ℛₖ (S : List Kind -> Ty -> Prop) : List Kind -> Ty -> Prop
| Δ1, t => ∀ {r Δ2}, Δ1 -⟨r⟩> Δ2 -> S Δ2 t[r]

mutual
  inductive Kinding.SnNor : (List Kind -> Ty -> Prop) -> KSet
  -- | lam :
  --   ℛₖ S1 Δ (λ[A] t) ->
  --   SnNor S2 (A::Δ) t B ->
  --   SnNor S1 Δ (λ[A] t) (A -:> B)
  | all :
    SnNor S (A::Δ) t ★ ->
    SnNor S Δ (∀[A] t) ★
  | arrow :
    SnNor S Δ A ★ ->
    SnNor S Δ B ★ ->
    SnNor S Δ (A -:> B) ★
  | neu :
    SnNeu S Δ A K ->
    SnNor S Δ A K
  -- | red :
  --   SnRed Δ S A A' ->
  --   SnNor Δ S A' K ->
  --   SnNor Δ S A K

  inductive Kinding.SnNeu : (List Kind -> Ty -> Prop) -> KSet
  | var :
    Δ[x]? = some K ->
    SnNeu S Δ t#x K
  -- | app :
  --   SnNeu S1 Δ f (A -:> B) ->
  --   SnNor S2 Δ a A ->
  --   SnNeu S3 Δ (f • a) B

  -- inductive Kinding.SnRed : (List Kind -> Ty -> Prop) -> KRed
  -- | beta :
  --   SnNor S1 Δ t A ->
  --   Δ ⊢ₖ λ[A] b : (A -:> B) ->
  --   SnRed S2 Δ ((λ[A] b) • t) b[su t::+0]
  -- | app :
  --   SnRed S1 Δ f f' ->
  --   SnRed S2 Δ (f • a) (f' • a)
end

mutual
  theorem Kinding.SnNor.soundness : SnNor S Δ A K -> Δ ⊢ₖ A : K
  --| .lam h1 h2 => Kinding.lam (Kinding.SnNor.soundness h2)
  | .all h1 => Kinding.all (Kinding.SnNor.soundness h1)
  | .arrow h1 h2 => Kinding.arrow (Kinding.SnNor.soundness h1) (Kinding.SnNor.soundness h2)
  | .neu h1 => Kinding.SnNeu.soundness h1
  --| .red h1 h2 => Kinding.SnRed.soundness h1 (Kinding.SnNor.soundness h2)

  theorem Kinding.SnNeu.soundness : SnNeu S Δ A K -> Δ ⊢ₖ A : K
  | .var h1 => Kinding.var h1
  -- | .app h1 h2 => Kinding.app (Kinding.SnNeu.soundness h1) (Kinding.SnNor.soundness h2)

  -- theorem Kinding.SnRed.soundness : SnRed S Δ A A' -> Δ ⊢ₖ A' : K -> Δ ⊢ₖ A : K
  -- | .beta h1 (.lam h2), j1 =>
  --   let lem := Kinding.beta h2 (Kinding.SnNor.soundness h1)
  --   let lem2 := Kinding.unique j1 lem
  --   Kinding.app (.lam h2) (Kinding.SnNor.soundness h1) |> cast (by rw [lem2])
  -- | .app h1, Kinding.app j1 j2 => Kinding.app (Kinding.SnRed.soundness h1 j1) j2
end

mutual
  theorem Kinding.SnNor.rename (m : Δ1 -⟨r⟩> Δ2) : SnNor S Δ1 A K -> SnNor S Δ2 A[r] K
  -- | SnNor.lam (S2 := S2) (t := t) (A := A) (B := B) f th =>

  --   Kinding.SnNor.lam (S2 := S2) (t := t[r.to.lift]) (λ m' => f (.comp m m') |> cast (by simp)) (th.rename (m.lift A) |> cast (by rw [Ren.to_lift]))
  | .all (A := A) (t := t) h =>
    SnNor.all (h.rename (KindingRen.lift A m)) |> cast (by rw [Ren.to_lift]; simp)
  | .arrow h1 h2 => .arrow (h1.rename m) (h2.rename m)
  | .neu h => .neu (h.rename m)
  -- | .red h1 h2 => .red (h1.rename m) (h2.rename m)

  theorem Kinding.SnNeu.rename (m : Δ1 -⟨r⟩> Δ2) : SnNeu S Δ1 A K -> SnNeu S Δ2 A[r] K
  | .var h => .var (m.act h)
  -- | .app h1 h2 => .app (h1.rename m) (h2.rename m)

  -- theorem Kinding.SnRed.rename (m : Δ1 -⟨r⟩> Δ2) : SnRed S Δ1 A B -> SnRed S Δ2 A[r] B[r]
  -- | .beta (S1 := S1) (t := t) (A := A) (b := b) h j => by
  --   have lem1 := (Kinding.subst (KindingRen.to m) j)
  --   simp at lem1
  --   have lem := SnRed.beta (S2 := S) (b := b[.re 0 :: r ∘ +1]) (.rename m h) lem1
  --   simp at *
  --   apply lem
  -- | .app h => .app (h.rename m)
end

@[simp]
def 𝒱ₖ : Kind -> List Kind -> Ty -> Prop
--| A -:> B, Δ, λ[_] t => ∀ {a}, Kinding.SnNor (𝒱ₖ A) Δ a A -> Kinding.SnNor (𝒱ₖ B) Δ t[su a::+0] B
| _, _, _ => False

structure Kinding.SemSubst (Δ1 Δ2 : List Kind) (σ : Subst Ty) where
  act : ∀ {i T}, Δ1[i]? = some T -> SnNor (𝒱ₖ T) Δ2 (σ.act i) T

notation:35 Γ:35 " -⟦" σ "⟧> " Δ:35 => Kinding.SemSubst Γ Δ σ

theorem Kinding.SemSubst.id : Δ -⟦+0⟧> Δ := .mk (λ h => SnNor.neu (SnNeu.var h))

theorem Kinding.SemSubst.lift (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := SemSubst.mk @λ i _ h =>
  match i with
  | 0 => SnNor.neu (SnNeu.var h)
  | _ + 1 => by
    simp_all
    have e1 := m.act h
    have lem := SnNor.rename (Δ2 := A :: Δ) (KindingRen.succ (X := Δ)) e1
    simp at lem
    apply lem

theorem Kinding.SemSubst.compose (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> Ξ) : Γ -⟦σ ∘ r.to⟧> Ξ := SemSubst.mk @λ i _ h =>
  have e2 := m1.act h
  SnNor.rename m2 e2 |> cast (by simp)

theorem Kinding.SemSubst.su (j : SnNor (𝒱ₖ A) Δ a A) (m : Γ -⟦σ⟧> Δ) : A::Γ -⟦su a::σ⟧> Δ := SemSubst.mk @ λ i _ h =>
  match i with
  | 0 => by simp_all
  | _ + 1 => m.act h

@[simp]
def SemanticKinding (Δ1 : List Kind) (A : Ty) (K : Kind) :=
  ∀ {σ Δ2}, Δ1 -⟦σ⟧> Δ2 -> Kinding.SnNor (𝒱ₖ K) Δ2 A[σ] K

notation:170 Γ:170 " ⊨ₖ " t:170 " : " A:170 => SemanticKinding Γ t A

-- theorem Kinding.app_induction:
--   S = 𝒱ₖ (A -:> K) ->
--   T = A -:> K ->
--   SnNor S Δ2 f T ->
--   SnNor (𝒱ₖ A) Δ2 a A ->
--   SnNor (𝒱ₖ K) Δ2 (f • a) K
-- | eq1, eq2, SnNor.lam (t := t) h1 h2, j2 =>
--   let lem2 : (λ x => x) = @id Nat := by unfold id; rfl
--   let lem : SnNor (𝒱ₖ K) Δ2 t[su a :: +0] K := by
--     subst eq1
--     simp [ℛₖ] at h1
--     replace h1 := h1 (KindingRen.id Δ2) j2
--     apply h1
--   have lem3 := Kinding.SnNor.soundness h2
--   SnNor.red (SnRed.beta (by simp at eq2; rcases eq2 with ⟨e1,e2⟩; rw [<-e1]at j2; apply j2) (Kinding.lam lem3)) lem
-- | eq1, eq2, .neu h, j2 => by subst eq1 eq2; apply SnNor.neu (SnNeu.app h j2)
-- | eq1, eq2, .red h1 h2, j2 => SnNor.red (SnRed.app h1) (Kinding.app_induction eq1 eq2 h2 j2)

theorem Kinding.fundamental : Δ ⊢ₖ A : K -> Δ ⊨ₖ A : K
| var j, σ, Δ2, h => h.act j
-- | lam (A := A) (t := t) (B := B) j, σ, Δ2, h =>
--   let j' : (A :: Δ) ⊨ₖ t : B := fundamental j
--   have lem {Δ2' r} : Δ2 -⟨r⟩> Δ2' → 𝒱ₖ (A -:> B) Δ2' (λ[A] t[σ.lift][r.to.lift]) := λ j1 T j2 =>
--     j' (SemSubst.su (a := T) j2 (SemSubst.compose h j1)) |> cast (by simp)
--   SnNor.lam (t := t[σ.lift]) lem (j' (SemSubst.lift h A))
-- | app j1 j2, σ, Δ2, h =>
--   let j1' := fundamental j1 h
--   let j2' := fundamental j2 h
--   Kinding.app_induction rfl rfl j1' j2'
| all j, σ, Δ2, h => .all $ j.fundamental $ h.lift _
| arrow j1 j2, σ, Δ2, h => .arrow (j1.fundamental h) (j2.fundamental h)

end TwoSortHet
