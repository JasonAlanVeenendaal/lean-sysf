
import LeanSubst
import Banana.Typing
import Banana.Typing.Substitute
import Banana.Kinding.StrongNorm
--import Banana.Kinding.Value
import Banana.Reduction
import Banana.Model
open LeanSubst

namespace Banana
--naively following lean-sysf/OneSortHomArityGen/StrongNorm2.lean
def SnModelSet := Term -> Prop
def SnRedModelSet := Term -> Term -> Prop

--attempt
def ℛ (S : SnModelSet) : SnModelSet
| t => ∀ {r1 : Ren Term} {r2 : Ren Ty}, S t⟨r1, r2⟩

mutual
  inductive SnNor : SnModelSet -> SnModelSet
  | lam :
    ℛ S1 (λ[A] t) ->
    SnNor S2 t->
    --Δ ⊢ₖ A : ★ ->
    SnNor S1 (λ[A] t)
  | tlam :
    ℛ S1 (Λ[K] t) ->
    SnNor S2 t ->
    SnNor S1 (Λ[K] t)
  | neu :
    SnNeu S t ->
    SnNor S t
  | red :
    SnRed S2 t t' ->
    SnNor S t' ->
    SnNor S t

  inductive SnNeu : SnModelSet -> SnModelSet
  | var :
    --Γ[x]? = some A ->
    --Δ ⊢ₖ A : ★ ->
    SnNeu S #x
  | app :
    SnNeu S1 f ->
    SnNor S2 a ->
    SnNeu S3 (f • a)
  | tapp :
    SnNeu S1 f ->
    --P' = P[su a .: Subst.id Ty] ->
    --Kinding.SnNor S2 Δ a K ->
    SnNeu S3 (f •[a])

  inductive SnRed : SnModelSet -> SnRedModelSet
  | beta :
    SnNor S1 t ->
    --Δ&Γ ⊢ (λ[A]b) : (A -:> B) ->
    SnRed S2 ((λ[A] b) • t) b[su t .: 𝐬0, .id Ty]
  | tbeta :
    --Δ ⊢ₖ t : K ->
    --Δ&Γ ⊢ (Λ[K] b) : (∀[K] P) ->
    --P' = P[su t.:(.id Ty)] ->
    SnRed S ((Λ[K] b) •[t]) b[.id Term, su t .: (Subst.id Ty)]
  | app :
    --Δ&Γ ⊢ a : A ->
    SnRed S1 f f' ->
    --Δ&Γ ⊢ f' : (A -:> B) ->
    SnRed S2 (f • a) (f' • a)
  | tapp :
    --Δ ⊢ₖ a : K ->
    SnRed S1 f f' ->
    --Δ&Γ ⊢ f' : (∀[K] P) ->
    --P' = P[su a.:(.id Ty)] ->
    SnRed S2 (f •[a]) (f' •[a])
end

@[simp]
instance : Model SnModelSet where
A A B := fun
  | λ[_] t => ∀ (a : Action Term), SnNor A a -> SnNor B t[a .: Subst.id Term, .id Ty]
  | _ => False
Q P := fun
  | Λ[_] t => ∀ (A : SnModelSet) (a:Action Ty), SnNor (P A) t[.id Term, a.:Subst.id Ty]
  | _ => False

@[simp]
def 𝒱 (A : Ty) (ξ : Nat -> SnModelSet) := ⟦A⟧ ξ

@[simp]
def ℰ A ξ := SnNor (𝒱 A ξ)

@[simp]
def 𝒞 (Γ : List Ty) (ξ : Nat -> SnModelSet) (σ : Subst Term) : Prop :=
  ∀ i A, Γ[i]? = some A -> ℰ A ξ (σ.act i)

--might need this later
-- structure 𝒞' (Γ : List Ty) (ξ : Nat -> SnModelSet) (σ : Subst Term) where
--  act : ∀ {i : Nat}, Γ[i]? = some A -> ℰ A ξ (σ.act i)

--a type substitution is needed here. since we don't have a kinding environment I think we can get away with just adding a τ
@[simp]
def SemanticTyping (Δ : List Kind) (Γ : List Ty) (t : Term) (A : Ty) :=
∀ σ ξ (τ : Subst Ty), 𝒞 Γ ξ σ -> ℰ A ξ t[σ, τ]

local notation:170 Δ:170 "&" Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Δ Γ t A

namespace SnNor
  -- mutual
  --   theorem sound : SnNor A t -> SN Red t
  --   | .lam (A := T) h1 h2 => sorry
  --   | .tlam h1 h2 => sorry
  --   | .red h1 h2 => SnRed.sound h1 (sound h2)
  --   | .neu h1 => sorry

  --   theorem SnRed.sound : SnRed A t t' -> SN Red t' -> SN Red t
  --   | .beta h1, h2 => sorry
  --   | .tbeta, h2 => sorry
  --   | .app h1, h2 => sorry
  --   | .tapp h1, h2 => sorry

  -- end

  theorem var x : SnNor A #x := SnNor.neu SnNeu.var

  mutual
    theorem SnNor.rename (r : Ren Term) (s : Ren Ty) : SnNor A t -> SnNor A t⟨r,s⟩
    | .lam (S2 := S2) (t := t) h1 h2 =>
      let j := SnNor.rename r.lift s h2
      --let lem := HetRenIdCommute
      SnNor.lam (S2 := S2)
      (by simp [ℛ] at *;
          intro r1 s2
          replace h1 := @h1 (r >> r1) (s >> s2)
          simp at h1
          apply h1)
      j
    | .tlam (S2 := S2) (t := t) h1 h2 =>
      let j := SnNor.rename r s.lift h2
      SnNor.tlam (S2 := S2)
      (by simp; simp [ℛ] at *;
          intro r1 s1
          replace h1 := @h1 (r >> r1) (s >> s1)
          apply h1)
      j
    | .neu h1 => SnNor.neu (SnNeu.rename r s h1)
    | .red h1 h2 =>
      let h2' := SnNor.rename r s h2
      let h1' := SnRed.rename r s h1
      SnNor.red h1' h2'

    theorem SnNeu.rename (r : Ren Term) (s : Ren Ty) : SnNeu A t -> SnNeu A t⟨r, s⟩
    | .var (x := x) => .var
    | .app h1 h2 =>
      let h1' := SnNeu.rename r s h1
      let h2' := SnNor.rename r s h2
      SnNeu.app h1' h2'
    | .tapp h1 =>
      let h1' := SnNeu.rename r s h1
      SnNeu.tapp h1'

    theorem SnRed.rename (r : Ren Term) (s : Ren Ty) : SnRed A t t' -> SnRed A t⟨r,s⟩ t'⟨r,s⟩
    | .beta (S1 := S1) (S2 := S2) (t := t) (A := A) (b := b) h1 =>
      let h1' := SnNor.rename r s h1
      let lem := @SnRed.beta S1 t⟨r, s⟩ S2 A⟨s⟩ b⟨r.lift, s⟩
      by simp at *; simp at lem; apply lem; apply h1'
    | .tbeta (K := K) (b := b) (t := t) (S := S) =>
      let lem := SnRed.tbeta (b := b⟨r, s.lift⟩) (K := K) (S := S) (t := t⟨s⟩)
      by simp; simp at lem; apply lem
    | .app h1 =>
      let h1' := SnRed.rename r s h1
      SnRed.app h1'
    | .tapp h1 =>
      let h1' := SnRed.rename r s h1
      SnRed.tapp h1'

  end
end SnNor

namespace ℰ
  theorem weaken : ℰ (A[Subst.add Ty 1]) (B::ξ) = ℰ A ξ := by simp [ℰ]; congr 1

  theorem beta : ℰ (A[su t .: .id Ty]) ξ = ℰ A (𝒱 t ξ :: ξ) :=
  by
    simp [𝒱];
    congr 1;
    congr;
    funext n;
    cases n
    case _ =>
      simp
    case _ =>
      simp

  theorem rename (r : Ren Ty) : ℰ A (ξ ∘ r.act) t = ℰ A⟨r⟩ ξ t := by simp only [ℰ, 𝒱] at *; congr 1; rw [Model.rename]
end ℰ

namespace 𝒞
  theorem re :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (ξ) (re x .: σ)
  := by
    intro h; simp only [𝒞]; intro i
    cases i <;> simp
    case _ =>
      apply SnNor.neu SnNeu.var
    case _ n =>
      intro A j
      replace h := h n A j
      apply h

  theorem su :
    ℰ A ξ a ->
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) ξ (su a .: σ)
  := by
    intro h
    simp at *
    intro h1 i A' h3
    cases i <;> simp
    case _ =>
      simp at h3
      subst h3
      apply h
    case _ =>
      simp at h3
      apply h1
      apply h3

  theorem rename {r : Ren Term} {s : Ren Ty}: 𝒞 Γ ξ σ -> 𝒞 Γ ξ (σ >> ·[r.to, s.to]) := by
    intro h; simp [𝒞, ℰ] at *; intro i A j
    replace h := h i A j
    let lem := SnNor.SnNor.rename r s h
    simp at lem
    norm_subst
    simp
    exact lem

  theorem lift (s : Ren Ty) :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (ξ) (.re 0 .: (σ >> ·[Subst.add Term 1, s.to]))
  := by
    intro h; apply re; apply rename h

  theorem test :
    𝒞 Γ ξ σ ->
    𝒞 Γ⟨Ren.add Ty 1⟩ (A::ξ) σ
  := by
    intro h
    simp only [𝒞] at *
    intro i A' h1
    replace h1 := List.getElem_of_getElem? h1
    rcases h1 with ⟨r, e⟩
    rw [<-List.rmap_getElem (by simp at r; exact r)] at e
    rw [<-e]
    rw [Subst.stable (σ := ·[Subst.add Ty 1]) (by simp)]
    --norm_subst at e
    rw [ℰ.weaken (B := A)]
    apply h
    simp
end 𝒞

namespace ℰ
  theorem app :
    S = 𝒱 (A -:> B) ξ ->
    SnNor S f ->
    ℰ A ξ a ->
    ℰ B ξ (f • a)
  | eq, SnNor.lam (S2 := S2) j1 j2, h2 =>
    by
      simp [ℰ] at *;
      subst eq;
      simp [ℛ] at j1; replace j1 := @j1 (.id Term) (.id Ty); simp [Model.A] at j1;
      replace j1 := @j1 (su a) h2; --simp at j1
      apply SnNor.red; apply SnRed.beta; apply h2; apply j1; apply S2
  | eq, SnNor.neu j1, h2 => SnNor.neu (SnNeu.app j1 h2)
  | eq, SnNor.red (t' := f') j1 j2, h2 =>
    let lem1 := SnRed.app (S2 := ⟦B⟧ ξ) (a := a) j1
    let lem2 := app eq j2 h2
    SnNor.red lem1 lem2
  | eq, SnNor.tlam j1 j2, h2 =>
    by
      subst eq;
      simp [ℛ] at j1
      replace j1 := @j1 (.id Term) (.id Ty)
      simp [Model.A] at j1

  theorem tapp :
    S = 𝒱 (∀[K] P) ξ ->
    SnNor S f ->
    ℰ (P[su a.:.id Ty]) ξ (f •[b])
  | eq, SnNor.lam j1 j2 =>
    by subst eq; simp [ℛ] at j1; replace j1 := @j1 (.id Term) (.id Ty);
       simp [Model.Q] at j1
  | eq, SnNor.neu j1 => SnNor.neu (SnNeu.tapp j1)
  | eq, SnNor.red j1 j2 =>
    let lem1 := SnRed.tapp (S2 := ⟦∀[K]P⟧ ξ) (a := b) j1
    let lem2 := tapp (a := a) eq j2
    SnNor.red lem1 lem2
  | eq, SnNor.tlam (S2 := S2) j1 j2 =>
    by
      simp [ℰ] at *
      simp [ℛ] at j1
      subst eq
      replace j1 := @j1 (.id Term) (.id Ty)
      simp [Model.Q] at j1
      apply SnNor.red
      apply SnRed.tbeta
      let lem := @beta a P ξ
      simp at lem
      rw [lem]
      replace j1 := @j1 (⟦a⟧ ξ) (su b)
      apply j1
      apply S2

  theorem lam :
    ℛ (𝒱 (A -:> B) ξ) (λ[C] b) ->
    ℰ (A -:> B) ξ (λ[C] b)
  := by
    intro h
    apply SnNor.lam; apply h
    simp only [ℛ] at h; simp [Model.A] at h
    replace h := @h (Ren.add Term 1) (.id Ty) (re 0)
    simp at h
    apply h
    apply SnNor.neu (SnNeu.var)

  theorem tlam :
    ℛ (𝒱 (∀[K]P) ξ) (Λ[K]b) ->
    ℰ (∀[K]P) ξ (Λ[K]b)
  := by
    intro h
    apply SnNor.tlam; apply h
    simp only [ℛ] at h; simp [Model.Q] at h
    replace h := @h (.id Term) (.add Ty 1)
    simp at h
    replace h := h (ξ 0) (re 0)
    simp at h
    apply h
end ℰ

theorem fundamental {Γ : List Ty} : Δ&Γ ⊢ t : A -> Δ&Γ ⊨ t : A
| .var (x := x) j1 j2, σ, ξ, τ, h1 => let lem := h1 x A j1; simp% lem -- h x A j1
| .lam (t := t) (A := A) (B := B) j1 j2, σ, ξ, τ, h1 =>
  let j2' := fundamental j2
  by
    unfold SemanticTyping at j2'
    unfold ℰ at j2'
    apply ℰ.lam; --rw [Term.smap_promote, Term.Ty.smap_promote];
    simp only [ℛ]; simp; intro r s;
    simp [Model.A]
    intro a h2
    apply j2'
    cases a
    case _ =>
      apply 𝒞.re
      apply 𝒞.rename h1
    case _ =>
      apply 𝒞.su h2
      apply 𝒞.rename h1
| .app j1 j2, σ, ξ, τ, h1  =>
  let j1' := fundamental j1 σ ξ τ h1
  let j2' := fundamental j2 σ ξ τ h1
  ℰ.app rfl j1' j2'
| .tlam (K := K) (P := P) j, σ, ξ, τ, h1 =>
  let j' := fundamental j
  by
    apply ℰ.tlam; simp [Model.Q]; simp [ℛ]; simp only [SemanticTyping] at j'; simp only [ℰ] at j'
    intro r s A a
    apply j'
    simp
    apply 𝒞.rename
    apply 𝒞.test h1
| .tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, ξ, τ, h1 =>
  let j1' := fundamental j1 σ ξ τ h1
  let lem := ℰ.tapp (a := a) (b := a[τ]) rfl j1'
  by subst e; simp [ℰ] at lem; simp; apply lem

theorem id_context : 𝒞 Γ ξ (Subst.id Term) := by simp; intro i A h; apply SnNor.var

theorem sn : Δ&Γ ⊢ t : A -> SnNor (⟦A⟧ ξ) t := λ h =>
  let lem := fundamental h (Subst.id Term) (ξ) (Subst.id Ty) (id_context)
  lem |> cast (by simp)
