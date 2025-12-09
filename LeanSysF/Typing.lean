
import LeanSubst
import LeanSysF.Term

open LeanSubst

inductive Typing : List Term -> Term -> Term -> Prop where
| var {Γ T x} :
  Γ[x]? = .some T ->
  Typing Γ T ★ ->
  Typing Γ #x T
| arr {Γ A B} :
  Typing Γ A ★ ->
  Typing Γ B ★ ->
  Typing Γ (A -:> B) ★
| app {Γ A B f a} :
  Typing Γ f (A -:> B) ->
  Typing Γ a A ->
  Typing Γ (f :@ a) B
| lam {Γ A B t} :
  Typing Γ A ★ ->
  Typing (A::Γ) t (B[S]) ->
  Typing Γ (:λ[A] t) (A -:> B)
| tvar {Γ x} :
  Γ[x]? = .some ★ ->
  Typing Γ #x ★
| all {Γ P} :
  Typing (★::Γ) P ★ ->
  Typing Γ (:∀ P) ★
| tapp {Γ P P' f a} :
  Typing Γ f (:∀ P) ->
  Typing Γ a ★ ->
  P' = P[%a::I] ->
  Typing Γ (f :@[a]) P'
| tlam {Γ P t} :
  Typing (★::Γ) t P ->
  Typing Γ (Λ t) (:∀ P)

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

inductive ActionTyping : List Term -> Subst.Action Term -> Term -> Prop where
| su :
  Γ ⊢ t : A ->
  ActionTyping Γ (.su t) A
| re :
  Γ ⊢ #x : A ->
  ActionTyping Γ (.re x) A

notation:170 Γ:170 " ⊢a " t:170 " : " A:170 => ActionTyping Γ t A

def SubstTyping : List Term -> Subst Term -> (Nat -> Term) -> Prop
| Γ, σ, F => ∀ n, Γ ⊢a σ n : F n

notation:170 Γ:170 " ⊢σ " t:170 " : " A:170 => SubstTyping Γ t A

-- theorem typing_renaming_lift {Γ Δ} A {r : Ren} :
--   (∀ x T, Γ ⊢ #x : T -> Δ ⊢ #(r x) : T) ->
--   ∀ x T, (A::Γ) ⊢ #x : T -> (A::Δ) ⊢ #(r.lift x) : T
-- := by
-- intro h x T j
-- simp [Ren.lift]; cases x <;> simp at *
-- case _ =>
--   cases j; case _ j =>
--   apply Typing.var
--   simp at *; subst j; rfl
-- case _ x =>
--   cases j; case _ j =>
--   simp at j; apply Typing.var
--   simp; have lem := h x T (Typing.var j)
--   cases lem; case _ lem => ↑x
--   apply lem

theorem typing_renaming_lift {Γ Δ : List Term} (A : Term) {σ : Subst Var } :
  (∀ x (T : Term), Γ[x]? = .some T -> Δ[(σ x).var]? = .some (T[Coe.coe σ])) ->
  ∀ x (T : Term), (A :: Γ)[x]? = .some T
    -> (A[Coe.coe σ] :: Δ)[(σ.lift x).var]? = .some (T[Coe.coe σ.lift])
:= by
  sorry

theorem typing_weaken {Γ t A} Δ (σ : Subst Var) :
  Γ ⊢ t : A ->
  (∀ x (T : Term), Γ[x]? = .some T -> Δ[(σ x).var]? = .some (T[Coe.coe σ])) ->
  Δ ⊢ t[σ] : A[σ]
:= by
intro j h
induction j generalizing Δ σ
case var Γ T x j1 j2 ih =>
  simp; generalize zdef : σ x = z at *
  cases z <;> simp
  case _ y =>
    apply Typing.var
    have lem := h x T j1
    rw [zdef] at lem; simp at lem
    apply lem
    apply ih _ _ h
  case _ t =>
    cases t; case _ t p =>
    cases p; case _ y =>
    simp; apply Typing.var
    have lem := h x T j1
    rw [zdef] at lem; simp at lem
    apply lem
    apply ih _ _ h
case arr j1 j2 ih1 ih2 =>
  simp; apply Typing.arr
  apply ih1 _ _ h
  apply ih2 _ _ h
case app j1 j2 ih1 ih2 =>
  simp; apply Typing.app
  apply ih1 _ _ h
  apply ih2 _ _ h
case lam Γ A B t j1 j2 ih1 ih2 =>
  simp; apply Typing.lam
  apply ih1 _ _ h
  replace ih2 := ih2 (A[σ] :: Δ) (σ.lift) (typing_renaming_lift A h)
  simp at ih2; simp
  apply ih2
case tvar Γ x j =>
  simp; generalize zdef : σ x = z at *
  cases z <;> simp
  case _ y =>
    apply Typing.tvar
    have lem := h x ★ j
    rw [zdef] at lem; simp at lem
    apply lem
  case _ t =>
    cases t; case _ t p =>
    cases p; case _ y =>
    simp; apply Typing.tvar
    have lem := h x ★ j
    rw [zdef] at lem; simp at lem
    apply lem
case all j ih =>
  simp; apply Typing.all
  replace ih := ih (★ :: Δ) σ.lift (typing_renaming_lift ★ h)
  simp at ih; apply ih
case tapp j1 j2 j3 ih1 ih2 =>
  simp; apply Typing.tapp
  apply ih1 _ _ h
  apply ih2 _ _ h
  rw [j3]; simp
case tlam j ih =>
  simp; apply Typing.tlam
  replace ih := ih (★ :: Δ) σ.lift (typing_renaming_lift ★ h)
  simp at ih; apply ih

-- theorem typing_subst_lift {Γ Δ} A {σ : Subst Term} :
--   (∀ x T, Γ ⊢ #x : T -> Δ ⊢ ↑(σ x) : T) ->
--   ∀ x T, (A::Γ) ⊢ #x : T -> (A::Δ) ⊢ ↑(σ.lift x) : T
-- := by
-- intro h x T j
-- cases j; case _ j =>
-- cases x <;> simp at *
-- case _ => subst j; apply Typing.var; simp
-- case _ x =>
--   have h' := h _ _ (Typing.var j)
--   have lem := typing_weaken (A :: Δ) (λ x => x + 1) h' (by {
--     intro x T j2; simp
--     apply Typing.var; simp
--     cases j2; simp [*]
--   }); simp at lem
--   unfold Subst.compose; simp
--   generalize zdef : σ x = z at *
--   cases z <;> simp at *
--   apply lem
--   rw [SubstMapStable.apply_stable (σ := S) (by rw [to_S])] at lem
--   apply lem

-- theorem typing_subst {Γ t A} Δ (σ : Subst Term) :
--   Γ ⊢ t : A ->
--   (∀ x T, Γ ⊢ #x : T -> Δ ⊢ ↑(σ x) : T) ->
--   Δ ⊢ t[σ] : A
-- := by
-- intro j h
-- induction j generalizing Δ σ
-- case var T x j =>
--   replace h := h x T; simp
--   generalize zdef : σ x = z at *
--   cases z <;> simp at *
--   all_goals apply h; apply Typing.var j
-- case app j1 j2 ih1 ih2 =>
--   simp; apply Typing.app
--   apply ih1 _ _ h
--   apply ih2 _ _ h
-- case lam j ih =>
--   simp; apply Typing.lam
--   replace ih := ih _ _ (typing_subst_lift _ h)
--   simp at ih; apply ih

-- theorem typing_beta {Γ A B b t} : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ b[.su t::I] : B := by
-- intro j1 j2
-- apply typing_subst Γ (.su t::I) j1 (λ x T h => by {
--   simp; cases x <;> simp
--   case _ =>
--     cases h; case _ h =>
--     simp at h; subst h
--     apply j2
--   case _ x =>
--     cases h; case _ h =>
--     simp at h
--     apply Typing.var h
-- })
