
import LeanSubst
import LeanSysF.Term
import LeanSysF.FreeVar

open LeanSubst

inductive Kinding : Ctx Term -> Term -> Prop where
| var {Γ : Ctx Term} {x} :
  Γ[x] = ★ ->
  Kinding Γ #x
| arr {Γ A B} :
  Kinding Γ A ->
  Kinding Γ B ->
  Kinding Γ (A -:> B)
| all {Γ P} :
  Kinding (★::Γ) P ->
  Kinding Γ (:∀ P)

notation:170 Γ:170 " ⊢ " A:170 " type" => Kinding Γ A

theorem Ctx.strong_rename_lift {A : Term} {Δ Γ : Ctx Term} {r : Ren} B :
  (∀ x T, x + 1 ∈ A -> Γ[x] = T -> Δ[r x] = T[r]) ->
  ∀ x T, x ∈ A -> (B::Γ)[x] = T -> (B[r]::Δ)[r.lift x] = T[r.lift]
:= by
  intro h1 x T h2 h3
  cases x <;> simp at *
  case zero =>
    subst h3; simp [Ren.lift]
    rw [Ren.to_lift]; simp
  case succ x =>
    replace h1 := h1 x h2
    subst h3; simp [Ren.lift]
    rw [Ren.to_lift]; rw [h1]; simp

theorem Ctx.rename_lift {Δ Γ : Ctx Term} {r : Ren} B :
  (∀ x T, Γ[x] = T -> Δ[r x] = T[r]) ->
  ∀ x T, (B::Γ)[x] = T -> (B[r]::Δ)[r.lift x] = T[r.lift]
:= by
  intro h1 x T h3
  cases x <;> simp at *
  case zero =>
    subst h3; simp [Ren.lift]
    rw [Ren.to_lift]; simp
  case succ x =>
    replace h1 := h1 x
    subst h3; simp [Ren.lift]
    rw [Ren.to_lift]; rw [h1]; simp

theorem Ctx.subst_re_lift {Γ Δ : Ctx Term} A {σ : Subst Term} :
  (∀ x T y, Γ[x] = T -> σ x = re y -> Δ[y] = T[σ]) ->
  ∀ x T y, (A::Γ)[x] = T -> σ.lift x = re y -> (A[σ]::Δ)[y] = T[σ.lift]
:= by
  intro h1 x T y h2 h3
  cases x <;> simp at *
  case zero => subst h2; subst h3; simp
  case succ x =>
    simp [Subst.compose] at h3
    generalize zdef : σ x = z at *
    cases z <;> simp at h3
    case _ z =>
    subst h3
    replace h1 := h1 x Γ[x] z rfl zdef
    subst h2; simp; rw [h1]; simp

theorem Kinding.strong_rename {Γ A} (Δ : Ctx Term) (r : Ren) :
  Γ ⊢ A type ->
  (∀ x T, x ∈ A -> Γ[x] = T -> Δ[r x] = T[r]) ->
  Δ ⊢ A[r] type
:= by
  intro j h
  induction j generalizing Δ r
  case var Γ x j =>
    replace h := h x ★ FV.found j; simp at h
    simp; apply Kinding.var h
  case arr Γ A B j1 j2 ih1 ih2 =>
    have h1 := λ x T (e : x ∈ A) => h x T (by simp; apply Or.inl e)
    have h2 := λ x T (e : x ∈ B) => h x T (by simp; apply Or.inr e)
    simp; apply Kinding.arr
    apply ih1 Δ r h1
    apply ih2 Δ r h2
  case all Γ P j ih =>
    have h2 : ∀ x T, x + 1 ∈ P -> Γ[x] = T -> Δ[r x] = T[r] := by
      intro x T q1 q2; simp at h
      replace h := h x q1; subst q2
      apply h
    simp; apply Kinding.all
    have lem1 := Ctx.strong_rename_lift ★ h2; simp at lem1
    have lem2 := ih (★::Δ) r.lift; simp at lem2
    replace lem2 := lem2 lem1
    rw [Ren.to_lift] at lem2; simp at lem2; exact lem2

theorem Kinding.rename {Γ A} (Δ : Ctx Term) (r : Ren) :
  Γ ⊢ A type ->
  (∀ x T, Γ[x] = T -> Δ[r x] = T[r]) ->
  Δ ⊢ A[r] type
:= by
  intro j h
  apply strong_rename _ _ j _
  intro x T h1 h2
  apply h x T h2

theorem Kinding.weaken : Γ ⊢ A type -> (P::Γ) ⊢ A[+1] type := by
  intro j
  have lem := rename (P::Γ) (· + 1) j
  simp at lem; exact lem

theorem Kinding.strengthen : (P::Γ) ⊢ A[+1] type -> Γ ⊢ A type := by
  intro j
  have lem := strong_rename Γ (· - 1) j (by {
    intro x T h1 h2
    cases x <;> simp at *
    case zero => exfalso; apply FV.zero_not_in_succ h1
    case succ x => subst h2; simp
  })
  simp at lem; apply lem

theorem Kinding.subst_lift {Γ Δ : Ctx Term} A {σ : Subst Term} :
  (∀ x t, Γ[x] = ★ -> σ x = su t -> Δ ⊢ t type) ->
  ∀ x t, (A::Γ)[x] = ★ -> σ.lift x = su t -> (A[σ]::Δ) ⊢ t type
:= by
  intro h1 x t h2 h3
  cases x <;> simp at *
  case _ x =>
  replace h2 := Term.ren_eq_star h2
  simp [Subst.compose] at h3
  generalize zdef : σ x = z at *
  cases z <;> simp at *
  case _ s =>
  subst h3
  replace h1 := h1 x s h2 zdef
  have lem := rename (A[σ]::Δ) (· + 1) h1
  simp at lem; exact lem

theorem Kinding.subst {Γ A} (Δ : Ctx Term) (σ : Subst Term) :
  Γ ⊢ A type ->
  (∀ x T y, Γ[x] = T -> σ x = re y -> Δ[y] = T[σ]) ->
  (∀ x t, Γ[x] = ★ -> σ x = su t -> Δ ⊢ t type) ->
  Δ ⊢ A[σ] type
:= by
  intro j h1 h2
  induction j generalizing Δ σ
  case var Γ x j =>
    simp; generalize zdef : σ x = z at *
    cases z <;> simp at *
    case _ y =>
      apply Kinding.var
      have lem := h1 x ★ y j zdef; simp at lem
      exact lem
    case _ t => apply h2 x t j zdef
  case arr Γ A B j1 j2 ih1 ih2 =>
    simp; apply Kinding.arr
    apply ih1 Δ σ h1 h2
    apply ih2 Δ σ h1 h2
  case all Γ P j ih =>
    -- TODO: Why does Lean unfold Subst.lift?
    have lem0 : ★[σ] = ★ := by simp
    have lem1 := Ctx.subst_re_lift ★ h1; rw [lem0] at lem1
    have lem2 := Kinding.subst_lift ★ h2; rw [lem0] at lem2
    simp; apply Kinding.all
    have lem3 := ih (★::Δ) σ.lift lem1 lem2; simp at lem3
    exact lem3

theorem Kinding.beta : (A::Γ) ⊢ P type -> Γ ⊢ B type -> Γ ⊢ P[su B::+0] type := by
  intro j1 j2
  apply subst Γ (su B::+0) j1
  case _ =>
    intro x T y h1 h2
    cases x <;> simp at *
    case _ n => subst h1; subst h2; simp
  case _ =>
    intro x t h1 h2
    cases x <;> simp at *
    case zero =>
      replace h1 := Term.ren_eq_star h1
      subst h1; subst h2; apply j2

theorem Kinding.injection_arrow : Γ ⊢ (A -:> B) type -> Γ ⊢ A type ∧ Γ ⊢ B type := by
  intro j; generalize zdef : A -:> B = z at *
  cases j; all_goals injection zdef
  case arr A' B' j1 j2 e1 e2 =>
    have lem1 : ∀ x, (λ i => mk2 A B i) x = (λ i => mk2 A' B' i) x := by
      intro x; rw [e2]
    have lem2 := lem1 0; simp [mk2] at lem2
    have lem3 := lem1 1; simp [mk2] at lem3
    subst lem2; subst lem3
    apply And.intro j1 j2
