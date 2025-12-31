
import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding

open LeanSubst

inductive Typing : Ctx Term -> Term -> Term -> Prop where
| var {Γ : Ctx Term} {T x} :
  Γ[x] = T ->
  Γ ⊢ T type ->
  Typing Γ #x T
| app {Γ A B f a} :
  Typing Γ f (A -:> B) ->
  Typing Γ a A ->
  Typing Γ (f :@ a) B
| lam {Γ A B t} :
  Γ ⊢ A type ->
  Typing (A::Γ) t B[+1] ->
  Typing Γ (:λ[A] t) (A -:> B)
| tapp {Γ} {P P' : Term} {f a} :
  Typing Γ f (:∀ P) ->
  Γ ⊢ a type ->
  P' = P[su a::+0] ->
  Typing Γ (f :@[a]) P'
| tlam {Γ P t} :
  Typing (★::Γ) t P ->
  Typing Γ (Λ t) (:∀ P)

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

theorem Kinding.type_not_term : Γ ⊢ A type -> ¬ (Γ ⊢ A : T) := by
  intro j1 j2; induction j1
  all_goals try solve | cases j2
  case var Γ x h1 =>
    cases j2; case _ h2 h3 =>
    rw [h1] at h3; subst h3; cases h2

theorem Typing.term_not_type : Γ ⊢ t : A -> ¬ (Γ ⊢ t type) := by
  intro j1 j2; induction j1
  all_goals try solve | cases j2
  case var Γ T x h1 h2 =>
    cases j2; case _ h3 =>
    rw [h1] at h3; subst h3; cases h2

theorem Typing.type_is_type : Γ ⊢ t : A -> Γ ⊢ A type := by
  intro j; induction j
  case var j => exact j
  case app j1 j2 ih1 ih2 =>
    replace ih1 := Kinding.injection_arrow ih1
    apply ih1.2
  case lam j1 j2 ih =>
    replace ih := Kinding.beta ih j1; simp at ih
    apply Kinding.arr j1 ih
  case tapp j1 j2 j3 ih =>
    cases ih; case _ ih =>
    replace ih := Kinding.beta ih j2
    subst j3; apply ih
  case tlam j ih => apply Kinding.all ih

theorem Typing.rename (Δ : Ctx Term) (r : Ren) :
  Γ ⊢ t : A ->
  (∀ x T, Γ[x] = T -> Δ[r x] = T[r]) ->
  Δ ⊢ t[r] : A[r]
:= by
  intro j h
  induction j generalizing Δ r
  case var Γ T x j1 j2 =>
    simp; apply Typing.var
    apply h x T j1
    apply Kinding.rename _ _ j2 h
  case lam Γ A B t j1 j2 ih =>
    replace ih := ih (A[r]::Δ) r.lift (Ctx.rename_lift A h)
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    simp; apply Typing.lam
    apply Kinding.rename _ _ j1 h
    simp; apply ih
  case app Γ A B f a j1 j2 ih1 ih2 =>
    replace ih1 := ih1 Δ r h; simp at ih1
    simp; apply Typing.app
    apply ih1
    apply ih2 Δ r h
  case tlam Γ P t j ih =>
    replace ih := ih (★[r]::Δ) r.lift (Ctx.rename_lift ★ h)
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    simp; apply Typing.tlam ih
  case tapp Γ P P' f a j1 j2 j3 ih =>
    replace ih := ih Δ r h; simp at ih
    simp; apply Typing.tapp ih
    apply Kinding.rename _ _ j2 h
    subst j3; simp

theorem Typing.weaken B : Γ ⊢ t : A -> (B::Γ) ⊢ t[+1] : A[+1] := by
  intro j
  have lem := rename (B::Γ) (· + 1) j
  simp at lem; exact lem

theorem Typing.subst_lift {σ : Subst Term} {Γ Δ : Ctx Term} A :
  (∀ x T t, Γ[x] = T -> Γ ⊢ T type -> σ x = su t -> Δ ⊢ t : T[σ]) ->
  ∀ x T t, (A::Γ)[x] = T -> (A::Γ) ⊢ T type -> σ.lift x = su t -> (A[σ]::Δ) ⊢ t : T[σ.lift]
:= by
  intro h1 x T t h2 h3 h4
  cases x <;> simp at *
  case _ x =>
  unfold Subst.compose at h4; simp at h4
  generalize zdef : σ x = z at *
  cases z <;> simp at *
  case _ s =>
  subst h4; subst h2
  have lem := h1 x Γ[x] s rfl (Kinding.strengthen h3) zdef
  have lem2 := weaken (A[σ]) lem
  simp at *; apply lem2

theorem Typing.subst (Δ : Ctx Term) (σ : Subst Term) :
  Γ ⊢ t : A ->
  (∀ x T y, Γ[x] = T -> σ x = re y -> Δ[y] = T[σ]) ->
  (∀ x t, Γ[x] = ★ -> σ x = su t -> Δ ⊢ t type) ->
  (∀ x T t, Γ[x] = T -> Γ ⊢ T type -> σ x = su t -> Δ ⊢ t : T[σ]) ->
  Δ ⊢ t[σ] : A[σ]
:= by
  intro j h1 h2 h3
  induction j generalizing Δ σ
  case var Γ T x j1 j2 =>
    simp; generalize zdef : σ x = z
    cases z <;> simp
    case _ z =>
      have lem := h1 x T z j1 zdef
      apply Typing.var lem
      apply Kinding.subst Δ σ j2 h1 h2
    case _ t => apply h3 x T t j1 j2 zdef
  case lam Γ A B t j1 j2 ih =>
    have lem := Kinding.subst Δ σ j1 h1 h2
    simp; apply Typing.lam lem
    replace ih := ih (A[σ]::Δ) σ.lift
      (Ctx.subst_re_lift A h1)
      (Kinding.subst_lift A h2)
      (subst_lift A h3)
    simp at *; apply ih
  case app ih1 ih2 =>
    replace ih1 := ih1 Δ σ h1 h2 h3; simp at ih1
    simp; apply Typing.app
    apply ih1
    apply ih2 Δ σ h1 h2 h3
  case tlam ih =>
    simp; apply Typing.tlam
    replace ih := ih (★[σ]::Δ) σ.lift
      (Ctx.subst_re_lift ★ h1)
      (Kinding.subst_lift ★ h2)
      (subst_lift ★ h3)
    simp at *; apply ih
  case tapp Γ P P' f a j1 j2 j3 ih =>
    replace ih := ih Δ σ h1 h2 h3; simp at ih
    simp; apply Typing.tapp
    apply ih; apply Kinding.subst Δ σ j2 h1 h2
    subst j3; simp

theorem Typing.beta :
  (A::Γ) ⊢ t : T ->
  Γ ⊢ a : A ->
  Γ ⊢ t[su a::+0] : T[su a::+0]
:= by
  intro j1 j2
  apply subst Γ (su a::+0) j1
  case _ =>
    intro x T y h1 h2
    cases x <;> simp at *
    case _ x =>
    subst h1; subst h2; simp
  case _ =>
    intro x s h1 h2
    cases x <;> simp at *
    replace h1 := Term.ren_eq_star h1
    subst h1; subst h2
    have lem := type_is_type j2
    cases lem
  case _ =>
    intro x S s h1 h2 h3
    cases x <;> simp at *
    subst h1; subst h3; simp
    apply j2

theorem Typing.beta_type :
  (★::Γ) ⊢ t : T ->
  Γ ⊢ a type ->
  Γ ⊢ t[su a::+0] : T[su a::+0]
:= by
  intro j1 j2
  apply subst Γ (su a::+0) j1
  case _ =>
    intro x A y h1 h2
    cases x <;> simp at *
    case _ x =>
    subst h1; subst h2; simp
  case _ =>
    intro x s h1 h2
    cases x <;> simp at *
    subst h2; apply j2
  case _ =>
    intro x S s h1 h2 h3
    cases x <;> simp at *
    subst h1; subst h3
    cases h2

theorem Typing.lam_inv :
  Γ ⊢ :λ[C] t : (A -:> B) ->
  (A::Γ) ⊢ t : B[+1]
:= by
  intro j
  generalize zdef : (:λ[C] t) = z at j
  generalize wdef : (A -:> B) = w at j
  cases j
  all_goals try solve | (try injection zdef; try injection wdef)
  injection zdef with _ _ e1 e2; simp at e1; subst e1; subst e2
  injection wdef with _ _ e; simp at e
  rcases e with ⟨e1, e2⟩; subst e1; subst e2
  case _ j => exact j
