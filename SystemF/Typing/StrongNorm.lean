
import LeanSubst
import SystemF.Typing
import SystemF.Typing.Substitute
--import SystemF.Kinding.StrongNorm
--import SystemF.Kinding.Value
--import SystemF.Reduction
import SystemF.Model
open LeanSubst

namespace SystemF
--naively following lean-sysf/OneSortHomArityGen/StrongNorm2.lean
def SnModelSet := Term -> Prop
def SnModelRel := Term -> Term -> Prop

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

  inductive SnRed : SnModelSet -> SnModelRel
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
  | λ[_] t => ∀ (a : Action Term), SnNor A a -> SnNor B t[a .: .id Term, .id Ty]
  | _ => False
Q P := fun
  | Λ[_] t => ∀ (A : SnModelSet) (a:Action Ty), SnNor (P A) t[.id Term, a .: .id Ty]
  | _ => False

@[simp]
def 𝒱 (A : Ty) (ξ : Nat -> SnModelSet) := ⟦A⟧ ξ

@[simp]
def ℰ A ξ := SnNor (𝒱 A ξ)

@[simp]
def 𝒞 (Γ : List Ty) (ξ : Nat -> SnModelSet) (σ : Subst Term) : Prop :=
  ∀ i A, Γ[i]? = some A -> ℰ A ξ (σ.act i)

@[simp]
def SemanticTyping (_ : List Kind) (Γ : List Ty) (t : Term) (A : Ty) :=
∀ σ ξ (τ : Subst Ty), 𝒞 Γ ξ σ -> ℰ A ξ t[σ, τ]

local notation:170 Δ:170 "&" Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Δ Γ t A

namespace SnNor
  theorem var x : SnNor A #x := SnNor.neu SnNeu.var

  mutual
    theorem SnNor.rename (r : Ren Term) (s : Ren Ty) : SnNor A t -> SnNor A t⟨r,s⟩
    | .lam (S2 := S2) (t := t) h1 h2 =>
      let j := SnNor.rename r.lift s h2
      SnNor.lam (S2 := S2) (@λ r1 s2 => simp% @h1 (r >> r1) (s >> s2)) j
    | .tlam (S2 := S2) (t := t) h1 h2 =>
      let j := SnNor.rename r s.lift h2
      SnNor.tlam (S2 := S2) (@λ r1 s1 => simp% @h1 (r >> r1) (s >> s1)) j
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
      lem h1' |> cast (by simp)
    | .tbeta (K := K) (b := b) (t := t) (S := S) =>
      let lem := SnRed.tbeta (b := b⟨r, s.lift⟩) (K := K) (S := S) (t := t⟨s⟩)
      lem |> cast (by simp)
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
  := λ h i A' j =>
    match i with
    | 0 => SnNor.neu SnNeu.var
    | n + 1 => h n A' j

  theorem su :
    ℰ A ξ a ->
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) ξ (su a .: σ)
  := λ h h1 i A' h3 =>
    match i with
    | 0 => h |> cast (by simp at h3; subst h3; simp)
    | n + 1 => by simp at h3; apply h1; apply h3

  theorem rename {r : Ren Term} {s : Ren Ty}: 𝒞 Γ ξ σ -> 𝒞 Γ ξ (σ >> ·[r.to, s.to])
  := λ h i A j =>
    let lem := SnNor.SnNor.rename r s (h i A j)
    lem |> cast (by simp at *; norm_subst)

  theorem lift (s : Ren Ty) :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (ξ) (.re 0 .: (σ >> ·[Subst.add Term 1, s.to]))
  := λ h => re (rename h)

  theorem weaken :
    𝒞 Γ ξ σ ->
    𝒞 Γ⟨Ren.add Ty 1⟩ (A::ξ) σ :=
    -- λ h i A' h1 =>
    -- have ⟨r, e⟩ := List.getElem_of_getElem? h1
    -- have lem1 := Subst.stable (S := Ty) (σ := ·[Subst.add Ty 1]) (r := ·⟨Ren.add Ty 1⟩)
    -- have lem2 := ℰ.weaken (B := A) (ξ := ξ) (A := Γ[i][Subst.add Ty 1])
    -- sorry
    by
    intro h
    simp only [𝒞] at *
    intro i A' h1
    replace h1 := List.getElem_of_getElem? h1
    rcases h1 with ⟨r, e⟩
    rw [<-List.rmap_getElem (by simp at r; exact r)] at e
    rw [<-e]
    rw [Subst.stable (σ := ·[Subst.add Ty 1]) (by simp)]
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
  | eq, SnNor.lam (A := A') (t := t) (S2 := S2) j1 j2, h2 =>
    have lem1 := @j1 (.id Term) (.id Ty)
    have lem2 : 𝒱 (A -:> B) ξ (λ[A']t)⟨𝐫0(Term), 𝐫0(Ty)⟩ := lem1 |> cast (by rw [eq])
    have lem3 : SnNor (⟦ B ⟧ ξ) t[(su a .: 𝐬0(Term)) .: SubstVec.id [Ty],] := @lem2 (su a) h2 |> cast (by simp)
    SnNor.red (S2 := S2) (SnRed.beta h2) (lem3)
  | eq, SnNor.neu j1, h2 => SnNor.neu (SnNeu.app j1 h2)
  | eq, SnNor.red (t' := f') j1 j2, h2 =>
    let lem1 := SnRed.app (S2 := ⟦B⟧ ξ) (a := a) j1
    let lem2 := app eq j2 h2
    SnNor.red lem1 lem2
  | eq, SnNor.tlam (K := K) (t := t) j1 j2, h2 =>
    have lem1 : ℛ (𝒱 (A -:> B) ξ) (Λ[K]t) := j1 |> cast (by rw [eq])
    have lem2 := @lem1 (.id Term) (.id Ty)
    lem2 |> cast (by simp at lem2; simp [Model.A] at lem2)

  theorem tapp :
    S = 𝒱 (∀[K] P) ξ ->
    SnNor S f ->
    ℰ (P[su a.:.id Ty]) ξ (f •[b])
  | eq, SnNor.lam (A := A) (t := t) j1 j2 =>
    have lem1 : ℛ (𝒱 (∀[K]P) ξ) (λ[A]t) := j1 |> cast (by rw [eq])
    have lem2 := @lem1 (.id Term) (.id Ty)
    lem2 |> cast (by simp [Model.Q] at lem2)
  | eq, SnNor.neu j1 => SnNor.neu (SnNeu.tapp j1)
  | eq, SnNor.red j1 j2 =>
    let lem1 := SnRed.tapp (S2 := ⟦∀[K]P⟧ ξ) (a := b) j1
    let lem2 := tapp (a := a) eq j2
    SnNor.red lem1 lem2
  | eq, SnNor.tlam (K := K') (t := t) (S2 := S2) j1 j2 =>
    have lem1 : ℛ (𝒱 (∀[K]P) ξ) (Λ[K']t) := j1 |> cast (by rw [eq])
    have lem2 : SnNor (⟦ P ⟧ (⟦ a ⟧ ξ)::ξ) t[𝐬0(Term), su b .: 𝐬0(Ty)] := @lem1 (.id Term ) (.id Ty) (⟦a⟧ ξ) (su b) |> cast (by simp)
    have lem3 := @beta a P ξ
    have lem4 : SnNor (⟦ P ⟧ ⟦ su a .: 𝐬0(Ty) ⟧ ξ) = SnNor (⟦ P ⟧ (⟦ a ⟧ ξ)::ξ) := lem3 |> cast (by simp)
    SnNor.red (S2 := S2) (SnRed.tbeta) (lem2 |> cast (by simp; rw [lem4]))

  theorem lam :
    ℛ (𝒱 (A -:> B) ξ) (λ[C] b) ->
    ℰ (A -:> B) ξ (λ[C] b)
  := λ h =>
    have lem : SnNor (⟦ A ⟧ ξ) #0 → SnNor (⟦ B ⟧ ξ) b := @h (Ren.add Term 1) (.id Ty) (re 0) |> cast (by simp)
    SnNor.lam h (lem (SnNor.neu SnNeu.var))

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
    apply ℰ.lam
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
    apply 𝒞.weaken h1
| .tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, ξ, τ, h1 =>
  let j1' := fundamental j1 σ ξ τ h1
  let lem := ℰ.tapp (a := a) (b := a[τ]) rfl j1'
  by subst e; simp [ℰ] at lem; simp; apply lem

theorem id_context : 𝒞 Γ ξ (Subst.id Term) := by simp; intro i A h; apply SnNor.var

theorem sn : Δ&Γ ⊢ t : A -> SnNor (⟦A⟧ ξ) t := λ h =>
  simp% fundamental h (Subst.id Term) (ξ) (Subst.id Ty) (id_context)

theorem preservation :
  ListWf (★ :: Δ) Γ⟨Ren.add Ty 1⟩ ->
  ListWf Δ Γ⟨Ren.add Ty 1⟩ ->
  ListWf Δ Γ -> Δ&Γ ⊢ t : A ->
  SnRed S t t' ->
  Δ&Γ ⊢ t' : A
| h0, h, j, .app (.lam h1 h3) h2, .beta j1 => Typing.beta j h3 h2
| h0, h, j, .app h1 h2, .app j1 => .app (preservation h0 h j h1 j1) h2
| h0, h, j, .tapp (K := K) (P := P) (.tlam h1) (a := a) h2 h3, .tbeta =>
  match K with
  | ★ => Typing.tbeta (t := a) (A := ★) h2 h0 h h1 |> cast (by subst h3; simp)
| h0, h, j, .tapp h1 h2 h3, .tapp j1 => .tapp (preservation h0 h j h1 j1) h2 h3

mutual
  theorem SnNor.consistency : SnNor S t -> ¬(Δ&[] ⊢ t : t#x)
  | .neu j, h => j.consistency h
  | .red j1 j2, h => j2.consistency (x := x) (preservation .nil .nil .nil h j1)

  theorem SnNeu.consistency : SnNeu S t ->  ¬(Δ&[] ⊢ t : T)
  | .app j1 _, .app h1 h2 => j1.consistency h1
  | .tapp j1, .tapp h1 _ h3 => j1.consistency h1
end

theorem consistency_lemma : SnNor S t -> ¬(Δ&[] ⊢ t : ∀[★]t#0)
| .tlam _ h2, .tlam j1 => h2.consistency j1
| .neu h1, j1 => h1.consistency j1
| .red h1 h2, j1 => consistency_lemma h2 (preservation .nil .nil .nil j1 h1)

theorem consistency : ¬(Δ&[] ⊢ t : ∀[★]t#0) := λ h =>
  consistency_lemma (sn h (ξ := (λ _ _ => True))) (Δ := Δ) h
