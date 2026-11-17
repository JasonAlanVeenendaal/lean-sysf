import SystemF.Typing
import SystemF.Kinding.Substitute
import SystemF.Typing.Rename
open LeanSubst

namespace SystemF

inductive ListWf : List Kind -> List Ty -> Prop where
| nil {Δ} : ListWf Δ []
| cons {Δ Γ A} : Δ ⊢ₖ A : ★ -> ListWf Δ Γ -> ListWf Δ (A::Γ)

theorem ListWf.get {Δ Γ T} {x : Nat} (wf : ListWf Δ Γ) (h : Γ[x]? = some T) : Δ ⊢ₖ T : ★ :=
  match wf, x with
  | .nil, _ => by cases h
  | .cons (A := A) j wf, 0 =>
    have e : A = T := by simp at h; exact h
    simp% [e] j
  | .cons j wf, x + 1 => wf.get h

structure TypingSubst (σ : Subst Term) (τ : Subst Ty) (Δ Δ' : List Kind) (Γ Γ' : List Ty) where
  ty : KindingSubst τ Δ Δ'
  act : ∀ {x} {T : Ty}, Γ[x]? = some T -> Δ'&Γ'[τ] ⊢ σ.act x : T[τ]

notation:1000 Δ:1000 " -[" τ "]> " Δ':1000 " ⊢ₛ " Γ:1000 " -[" σ "]> " Γ':1000 => TypingSubst σ τ Δ Δ' Γ Γ'

theorem TypingSubst.id Δ Γ : (ListWf Δ Γ) -> (TypingSubst (.id Term) (.id Ty) Δ Δ Γ Γ) := λ h =>
  ⟨.id Δ, λ {x} {T} j => .var (j |> cast (by simp)) (ListWf.get (x := x) h (simp% j))⟩

theorem TypingSubst.lift {σ τ Δ Δ' Γ Γ' A}
  (m : TypingSubst σ τ Δ Δ' Γ Γ') (wf : ListWf Δ A)
  : TypingSubst (σ.lift [Ty] A.length) τ Δ Δ' (A ++ Γ) (A ++ Γ')
:= ⟨m.ty, λ {x T} j =>
  match x.decLt A.length with
  | isTrue h =>
    have lem1 := List.getElem?_append_left h ▸ j
    have lem2 : x < A[τ].length := by simp [h]
    have j' : Δ'&(A[τ] ++ Γ'[τ]) ⊢ .var x : T[τ] := .var
      (by simp [List.getElem?_append_left lem2]; norm_subst [lem1])
      (.subst m.ty $ wf.get lem1)
    simp% [-Subst.lift, Subst.lift_act_lt h] j'
  | isFalse h =>
    have h : x ≥ A.length := by lia
    have lem1 := List.getElem?_append_right h ▸ j
    have lem2 := (m.act lem1).rename (.id Δ') (.add Γ'[τ] A[τ])
    simp% [-Subst.lift, Subst.lift_act_ge h] lem2⟩

theorem TypingSubst.lift_ty {σ τ Δ Δ' Γ Γ'} (m : TypingSubst σ τ Δ Δ' Γ Γ')
  : TypingSubst (σ >> RenVec.add [Term, Ty] [0, 1]) (τ.lift)
    (★ :: Δ) (★ :: Δ')
    Γ⟨.add Ty 1⟩ Γ'⟨.add Ty 1⟩
:= ⟨.lift ★ (m.ty), λ {x T} j =>
  have ⟨_, h⟩ := List.getElem?_eq_some_iff.1 j
  have lem1 := congrArg (λ x => x⟨.sub Ty 1⟩) j
  have lem2 := @m.act x T⟨.sub Ty 1⟩ $ simp% lem1
  simp% [<-h] lem2.rename (.succ (X := Δ') (A := ★)) (.id Γ'[τ])⟩

theorem Typing.subst
  (m : TypingSubst σ τ Δ1 Δ2 Γ1 Γ2) :
  Δ1&Γ1 ⊢ t : A -> Δ2&Γ2[τ] ⊢ t[σ,τ] : A[τ]
| var h j => m.act h
| lam (A := A) j1 j2 => lam (j1.subst m.ty) (simp% j2.subst $ m.lift (ListWf.cons j1 .nil))
| app j1 j2 => app (j1.subst m) (j2.subst m)
| tlam (K := K) j => tlam (simp% j.subst $ m.lift_ty)
| tapp j1 j2 e => tapp (j1.subst m) (j2.subst m.ty) (by simp [e])

theorem TypingSubst.su (j : Δ&Γ2 ⊢ a : A) (m : TypingSubst σ (.id Ty) Δ Δ Γ1 Γ2)
  : TypingSubst (su a .: σ) (.id Ty) Δ Δ (A::Γ1) Γ2 := ⟨m.ty, @λ x T h =>
    match x with
    | 0 => j |> cast (by simp at h; subst h; simp)
    | n + 1 => by simp; simp at h; let lem := m.act h; simp at lem; apply lem⟩

theorem Typing.beta :
  ListWf Δ Γ ->
  Δ&(A::Γ) ⊢ b : B ->
  Δ&Γ ⊢ t : A ->
  Δ&Γ ⊢ b[su t.:.id Term, .id Ty] : B
| j0, j1, j2 =>
  have lem := TypingSubst.su j2 (.id Δ Γ j0)
  have lem2 := Typing.subst (A := B) (t := b) lem
  lem2 j1 |> cast (by simp)

theorem TypingSubst.su_ty :
  ListWf (A::Δ) Γ ->
  Δ ⊢ₖ t : A ->
  TypingSubst (.id Term) (.su t .: .id Ty) (A :: Δ) Δ Γ Γ
:= λ j q =>
  ⟨KindingSubst.su q (KindingSubst.id Δ),
  @λ x T h => Typing.var (by norm_subst; rw [h]) (Kinding.subst (KindingSubst.su q (.id Δ)) (j.get h))⟩

theorem Typing.tbeta :
  Δ ⊢ₖ t : A ->
  ListWf (A::Δ) Γ ->
  ListWf Δ Γ ->
  (A::Δ)&Γ ⊢ b : B ->
  Δ&Γ[su t .: .id Ty] ⊢ b[.id Term, su t .: .id Ty] : B[su t .: .id Ty]
| q, j, _, j1 => Typing.subst (TypingSubst.su_ty j q) j1
