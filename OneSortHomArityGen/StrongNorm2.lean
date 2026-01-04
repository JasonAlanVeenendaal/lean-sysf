
import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding
import OneSortHomArityGen.Typing
import OneSortHomArityGen.Reduction
import OneSortHomArityGen.Progress
import OneSortHomArityGen.SN
import OneSortHomArityGen.Model

namespace OneSortHomArityGen
namespace Normalization.Version2

open LeanSubst

def SnModelSet := Term -> Prop

def ℛ (S : SnModelSet) : SnModelSet
| t => ∀ (r:Ren), S t[r]

inductive ℒ (S : SnModelSet) : SnModelSet where
| lift {t : Term} :
  (t.is_xlam -> ℛ S t) ->
  (∀ {t'}, t ~> t' -> ℒ S t') ->
  ℒ S t

@[simp]
instance : Model SnModelSet where
  A A B := fun
    | .bind .lam _ t => ∀ a, ℒ A a -> ℒ B t[su a::+0]
    | _ => False
  Q P := fun
    | .bind .tlam _ t => ∀ A a, Value a -> ℒ (P A) t[su a::+0]
    | _ => False
  P := Value

def 𝒱 (A : Term) (ξ : Nat -> SnModelSet) := ⟦ A ⟧ ξ

def ℰ A ξ := ℒ (𝒱 A ξ)

def 𝒞 (Γ : Ctx Term) (ξ : Nat -> SnModelSet) (σ : Subst Term) : Prop :=
  ∀ i, (Γ[i] ≠ ★ -> ℰ Γ[i] ξ (σ i))
    ∧ (Γ[i] = ★ -> Value (σ i))

@[simp]
def SemanticTyping (Γ : Ctx Term) (t : Term) (A : Term) :=
  ∀ σ ξ, 𝒞 Γ ξ σ -> ℰ A ξ t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

namespace ℒ
  theorem sound : ℒ A t -> SN Red t := by
    intro h; induction h; case _ s h1 h2 ih =>
    apply SN.sn; intro t' r; apply ih r

  theorem preservation : ℒ A t -> t ~> t' -> ℒ A t' := by
    intro h r; cases h; case _ h => apply h r

  theorem var x : ℒ A #x := by
    apply ℒ.lift; intro h; simp at h
    intro t' r; cases r

  theorem rename (r : Ren) : ℒ A t -> ℒ A t[r] := by
    intro h; induction h; case _ t' h1 h2 ih =>
    apply ℒ.lift
    case _ =>
      intro h; cases t' <;> simp at h
      case _ n v ts b =>
      cases v <;> simp at h
      all_goals (
        replace h1 := h1 (by simp)
        simp only [ℛ] at *; intro k
        replace h1 := h1 (k ∘ r)
        simp at *; apply h1
      )
    case _ =>
      intro t'' h
      have lem := Red.antirename r h
      rcases lem with ⟨z, h1, h2⟩; subst h2
      apply ih h1
end ℒ

namespace ℛ
  @[simp]
  theorem var : ℛ (𝒱 #x ξ) t <-> ∀ (r:Ren), ξ x t[r] := by
    apply Iff.intro
    case _ =>
      intro h r; simp [ℛ] at h
      replace h := h r; simp [𝒱] at h
      apply h
    case _ =>
      intro h; simp [ℛ]; intro r
      replace h := h r
      simp [𝒱]; exact h

  @[simp]
  theorem lam
    : ℛ (𝒱 (A -:> B) ξ) (:λ[C] b) <-> ∀ (r:Ren) a, ℰ A ξ a -> ℰ B ξ b[su a::r]
  := by
    apply Iff.intro
    case _ =>
      intro h r a ea; simp [ℛ] at h
      replace h := h r; simp [𝒱] at h
      simp [ℰ, 𝒱] at *
      apply h a ea
    case _ =>
      intro h; simp [ℛ]; intro r a va; simp at *
      replace h := h r a va
      apply h

  @[simp]
  theorem tlam
    : ℛ (𝒱 (:∀ P) ξ) (Λ b) <-> ∀ (r:Ren) A a, Value a -> ℰ P (A::ξ) b[su a::r]
  := by
    apply Iff.intro
    case _ =>
      intro h r A a va; simp [ℛ, 𝒱] at h
      replace h := h r A a va
      simp [ℰ, 𝒱]; apply h
    case _ =>
      intro h; simp [ℛ, 𝒱]; intro r A a va
      replace h := h r A a va
      apply h
end ℛ

namespace ℰ
  theorem weaken : ℰ (A[+1]) (B::ξ) = ℰ A ξ := by
    simp [ℰ]; congr 1; simp [𝒱]

  theorem beta : ℰ (A[su t::+0]) ξ = ℰ A (𝒱 t ξ :: ξ) := by
    simp [ℰ]; congr 1; simp [𝒱]

  theorem rename (r : Ren) : ℰ A (ξ ∘ r) t = ℰ A[r] ξ t := by
    simp only [ℰ, 𝒱] at *; congr 1; rw [Model.rename]
end ℰ

namespace 𝒞
  theorem term_su :
    A ≠ ★ ->
    ℰ A ξ t ->
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (su t::σ)
  := by
    intro ne h1 h2; simp only [𝒞]; intro i
    cases i <;> simp
    case _ =>
      apply And.intro
      intro _; rw [ℰ.weaken]; exact h1
      intro h; replace h := Term.ren_eq_star h
      exfalso; apply ne h
    case _ x =>
      apply And.intro
      intro h; replace h := Term.succ_not_star_implies_not_star h
      rw [ℰ.weaken]; apply (h2 x).1 h
      intro h; replace h := Term.ren_eq_star h
      apply (h2 x).2 h

  theorem type_su :
    A = ★ ->
    Value t ->
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (su t::σ)
  := by
    intro e h1 h2; simp only [𝒞]; intro i
    cases i <;> simp
    case _ => subst e; simp; exact h1
    case _ x =>
      apply And.intro
      intro h; replace h := Term.succ_not_star_implies_not_star h
      rw [ℰ.weaken]; apply (h2 x).1 h
      intro h; replace h := Term.ren_eq_star h
      apply (h2 x).2 h

  theorem re :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (re x::σ)
  := by
    intro h; simp only [𝒞]; intro i
    cases i <;> simp
    case _ =>
      apply And.intro <;> intro h
      apply ℒ.var; apply Value.var
    case _ i =>
      apply And.intro <;> intro h2
      replace h2 := Term.succ_not_star_implies_not_star h2
      rw [ℰ.weaken]; apply (h i).1 h2
      replace h2 := Term.ren_eq_star h2
      apply (h i).2 h2

  theorem rename {σ : Subst Term} (r : Ren) : 𝒞 Γ ξ σ -> 𝒞 Γ ξ (σ ∘ r.to) := by
    intro h; simp [𝒞, ℰ] at *; intro i
    replace h := h i
    apply And.intro
    case _ =>
      intro h2; have lem := ℒ.rename r (h.1 h2)
      simp at lem; exact lem
    case _ =>
      intro h2; have lem := Value.monotone r (h.2 h2)
      simp at lem; exact lem

  theorem weaken : 𝒞 Γ ξ σ -> 𝒞 Γ ξ (σ ∘ +1) := by
    intro h; have lem := rename (· + 1) h
    simp at lem; exact lem

  theorem lift S :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (.re 0::σ ∘ +1)
  := by
    intro h; apply re
    apply rename _ h
end 𝒞

namespace ℰ

  theorem ind2 {P : Term -> Term -> Prop} :
    (∀ s t,
      ℰ A ξ s ->
      ℰ B ζ t ->
      (∀ s', s ~> s' -> P s' t) ->
      (∀ t', t ~> t' -> P s t') ->
      P s t) ->
    ℰ A ξ s ->
    ℰ B ζ t ->
    P s t
  := by
    intro h j1 j2
    induction j1 generalizing t; case _ s' q1 q2 qih =>
    induction j2; case _ t' w1 w2 wih =>
    apply h; apply ℒ.lift q1 q2; apply ℒ.lift w1 w2
    intro s'' r; apply qih r; apply ℒ.lift w1 w2
    intro t'' r; apply wih r

  theorem app :
    ℰ (A -:> B) ξ f ->
    ℰ A ξ a ->
    ℰ B ξ (f :@ a)
  := by
    intro h1 h2
    apply ind2 _ h1 h2
    intro s t h1 h2 ih1 ih2
    apply ℒ.lift; simp; intro w r
    replace r := Red.app_inv r
    rcases r with ⟨A, b, e1, e2⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
    case _ =>
      subst e1 e2; cases h1; case _ h1 h3 =>
      simp at h1; replace h1 := h1 id t; simp at h1
      apply h1 h2
    case _ => subst e; apply ih1 _ r
    case _ => subst e; apply ih2 _ r

  theorem tapp a b :
    Value b ->
    ℰ (:∀ P) ξ f ->
    ℰ (P[su a::+0]) ξ (f :@[b])
  := by
    intro vb h; induction h; case _ t h1 h2 ih =>
    rw [ℰ.beta]; apply ℒ.lift; simp
    intro t' r; replace r := Red.tapp_inv r
    rcases r with ⟨t'', e1, e2⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
    case _ =>
      subst e1 e2; simp at h1
      replace h1 := h1 id (𝒱 a ξ) b vb; simp at h1
      exact h1
    case _ =>
      subst e; replace ih := ih r
      rw [ℰ.beta] at ih; exact ih
    case _ =>
      exfalso; apply Value.sound vb _ r

  theorem lam :
    SN Red b ->
    Value C ->
    ℛ (𝒱 (A -:> B) ξ) (:λ[C] b) ->
    ℰ (A -:> B) ξ (:λ[C] b)
  := by
    intro h1 v h2; induction h1; case _ x h1 ih1 =>
    apply ℒ.lift
    case _ => intro h3; exact h2
    case _ =>
      intro t' r
      replace r := Red.lam_inv r
      rcases r with ⟨A', e, r⟩ | ⟨b', e, r⟩
      case _ => exfalso; apply Value.sound v _ r
      case _ =>
        subst e; replace ih1 := ih1 _ r
        apply ih1; simp; intro k a ea
        have r2 : x[su a::k] ~> b'[su a::k] := Red.subst _ r
        apply ℒ.preservation _ r2
        simp at h2; apply h2 k a ea

  theorem tlam :
    SN Red b ->
    ℛ (𝒱 (:∀ P) ξ) (Λ b) ->
    ℰ (:∀ P) ξ (Λ b)
  := by
    intro h1 h2; induction h1; case _ x h1 ih1 =>
    apply ℒ.lift
    case _ => intro h3; exact h2
    case _ =>
      intro t' r
      replace r := Red.tlam_inv r
      rcases r with ⟨b', e, r⟩; subst e
      replace ih1 := ih1 _ r; apply ih1; simp
      intro k A a va
      have r2 : x[su a::k] ~> b'[su a::k] := Red.subst _ r
      apply ℒ.preservation _ r2
      simp at h2; apply h2 k A a va

end ℰ

theorem type_subst_value :
  𝒞 Γ ξ σ ->
  Γ ⊢ A type ->
  Value A[σ]
:= by
  intro h j
  induction j generalizing ξ σ
  case _ Γ x j =>
    simp; replace h := h x; rw [j] at h
    apply h.2 rfl
  case _ Γ A B j1 j2 ih1 ih2 =>
    simp; apply Value.ctor; simp
    apply Value.mk2 <;> simp
    apply ih1 h; apply ih2 h
  case _ Γ P j ih =>
    simp; apply Value.bind; simp
    replace ih := @ih (Model.P::ξ) σ.lift
    simp at ih; apply ih
    apply 𝒞.lift _ h

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A := by
  intro j; induction j <;> simp
  case var Γ T x j1 j2 =>
    intro σ ξ h; simp only [𝒞] at h
    have lem : Γ[x] ≠ ★ := by
      subst j1; apply Kinding.type_not_star j2
    subst j1; apply (h x).1 lem
  case app Γ A B f a j1 j2 ih1 ih2 =>
    intro σ ξ h; simp at ih1 ih2
    apply ℰ.app (ih1 σ ξ h) (ih2 σ ξ h)
  case lam Γ A B t j1 j2 ih =>
    intro σ ξ h; simp at ih
    apply ℰ.lam; apply ℒ.sound
    apply ih; apply 𝒞.lift Model.P (ξ := ξ) h
    apply type_subst_value h j1
    simp; intro r a ea
    have lem : A ≠ ★ := Kinding.type_not_star j1
    replace ih := @ih (su a::σ ∘ r.to) (Model.P::ξ) (by {
      apply 𝒞.term_su lem
      case _ => exact ea
      case _ => apply 𝒞.rename r h
    }); simp at ih
    rw [ℰ.weaken] at ih; exact ih
  case tapp Γ P P' f a j1 j2 j3 ih =>
    intro σ ξ h; simp at ih; subst j3
    apply ℰ.tapp _ _ _ (ih σ ξ h)
    apply type_subst_value h j2
  case tlam Γ P t j ih =>
    intro σ ξ h; simp at ih
    apply ℰ.tlam
    apply ℒ.sound; apply ih; apply 𝒞.lift Model.P (ξ := ξ) h
    simp; intro r A a va
    apply ih; apply 𝒞.type_su rfl va
    apply 𝒞.rename r; exact h

theorem strong_normalization : Γ ⊢ t : A -> SN Red t := by
  intro j; have lem := fundamental j; simp at lem
  replace lem := lem +0 (λ _ _ => True) (by {
    simp [𝒞]; intro i; apply And.intro <;> intro h
    simp [ℰ]; apply ℒ.var; apply Value.var
  }); simp at lem; simp [ℰ] at lem
  apply ℒ.sound lem

end Normalization.Version2
end OneSortHomArityGen
