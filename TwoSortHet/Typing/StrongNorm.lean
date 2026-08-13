
import LeanSubst
import TwoSortHet.Typing
import TwoSortHet.Typing.Substitute
import TwoSortHet.Kinding.StrongNorm
import TwoSortHet.Kinding.Value
import TwoSortHet.Reduction
import TwoSortHet.Model
open LeanSubst

namespace TwoSortHet

def TSet := List Kind -> List Ty -> Term -> Ty -> Prop
def TSet.empty : TSet := λ _ _ _ _ => False
def TRed := List Kind -> List Ty -> Term -> Term -> Ty -> Prop

def LR := List Kind -> List Ty -> Term -> Prop
def TRed' := List Kind -> List Ty -> Term -> Term -> Prop
--(A : Ty) -> (Nat -> KSet) -> (Δ : List Kind) -> (Γ : List Ty) -> (t : Term) ->  Prop

def ℛ (S : LR) : LR
| Δ, Γ1, t => ∀ {r Γ2}, Γ1 -⟨r⟩> Γ2 -> S Δ Γ2 t[r]

mutual
  inductive Typing.SnNor : LR -> TSet
  | lam :
    --Kinding.SnNor S Δ A K -> Value (A -:> B) ->
    ℛ S1 Δ Γ (λ[A] t) ->
    SnNor S2 Δ (A::Γ) t B ->
    Δ ⊢ₖ A : ★ ->
    SnNor S1 Δ Γ (λ[A] t) (A -:> B)
  | tlam :
    ℛ S1 Δ Γ (Λ[K] t) ->
    SnNor S2 (K::Δ) Γ⟨.add 1⟩ t P ->
    SnNor S1 Δ Γ (Λ[K] t) (∀[K] P)
  | neu :
    SnNeu S Δ Γ t A ->
    SnNor S Δ Γ t A
  | red :
    SnRed S2 Δ Γ t t' A ->
    SnNor S Δ Γ t' A ->
    SnNor S Δ Γ t A

  inductive Typing.SnNeu : LR -> TSet
  | var :
    Γ[x]? = some A ->
    Δ ⊢ₖ A : ★ ->
    SnNeu S Δ Γ #x A
  | app :
    SnNeu S1 Δ Γ f (A -:> B) ->
    SnNor S2 Δ Γ a A ->
    SnNeu S3 Δ Γ (f • a) B
  | tapp :
    SnNeu S1 Δ Γ f (∀[K] P) ->
    P' = P[su a::+0] ->
    Kinding.SnNor S2 Δ a K ->
    SnNeu S3 Δ Γ (f •[a]) P'

  inductive Typing.SnRed : LR -> TRed
  | beta :
    SnNor S1 Δ Γ t A ->
    Δ&Γ ⊢ (λ[A]b) : (A -:> B) ->
    SnRed S2 Δ Γ ((λ[A] b) • t) b[su t::+0] B
  | tbeta :
    Δ ⊢ₖ t : K ->
    Δ&Γ ⊢ (Λ[K] b) : (∀[K] P) ->
    P' = P[su t::+0] ->
    SnRed S Δ Γ ((Λ[K] b) •[t]) b[su t::+0:Ty] P'
  | app :
    Δ&Γ ⊢ a : A ->
    SnRed S1 Δ Γ f f' (A -:> B) ->
    Δ&Γ ⊢ f' : (A -:> B) ->
    SnRed S2 Δ Γ (f • a) (f' • a) B
  | tapp :
    Δ ⊢ₖ a : K ->
    SnRed S1 Δ Γ f f' (∀[K] P) ->
    Δ&Γ ⊢ f' : (∀[K] P) ->
    P' = P[su a::+0] ->
    SnRed S2 Δ Γ (f •[a]) (f' •[a]) P'
end

--trying to make this work with Model
mutual
  inductive Typing.SnNor' : LR -> LR
  | lam :
    --Kinding.SnNor S Δ A K -> Value (A -:> B) ->
    ℛ S1 Δ Γ (λ[A] t) ->
    SnNor' S2 Δ (A::Γ) t ->
    Δ ⊢ₖ A : ★ ->
    SnNor' S1 Δ Γ (λ[A] t)
  | tlam :
    ℛ S1 Δ Γ (Λ[K] t) ->
    SnNor' S2 (K::Δ) Γ⟨.add 1⟩ t ->
    SnNor' S1 Δ Γ (Λ[K] t)
  | neu :
    SnNeu' S Δ Γ t ->
    SnNor' S Δ Γ t
  | red :
    SnRed' S2 Δ Γ t t' ->
    SnNor' S Δ Γ t' ->
    SnNor' S Δ Γ t

  inductive Typing.SnNeu' : LR -> LR
  | var :
    Γ[x]? = some A ->
    Δ ⊢ₖ A : ★ ->
    SnNeu' S Δ Γ #x
  | app :
    SnNeu' S1 Δ Γ f ->
    SnNor' S2 Δ Γ a ->
    SnNeu' S3 Δ Γ (f • a)
  | tapp :
    SnNeu' S1 Δ Γ f ->
    P' = P[su a::+0] ->
    Kinding.SnNor S2 Δ a K ->
    SnNeu' S3 Δ Γ (f •[a])

  inductive Typing.SnRed' : LR -> TRed'
  | beta :
    SnNor' S1 Δ Γ t ->
    Δ&Γ ⊢ (λ[A]b) : (A -:> B) ->
    SnRed' S2 Δ Γ ((λ[A] b) • t) b[su t::+0]
  | tbeta :
    Δ ⊢ₖ t : K ->
    Δ&Γ ⊢ (Λ[K] b) : (∀[K] P) ->
    P' = P[su t::+0] ->
    SnRed' S Δ Γ ((Λ[K] b) •[t]) b[su t::+0:Ty]
  | app :
    Δ&Γ ⊢ a : A ->
    SnRed' S1 Δ Γ f f' ->
    Δ&Γ ⊢ f' : (A -:> B) ->
    SnRed' S2 Δ Γ (f • a) (f' • a)
  | tapp :
    Δ ⊢ₖ a : K ->
    SnRed' S1 Δ Γ f f' ->
    Δ&Γ ⊢ f' : (∀[K] P) ->
    P' = P[su a::+0] ->
    SnRed' S2 Δ Γ (f •[a]) (f' •[a])
end

mutual
  theorem Typing.SnNor.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnNor S Δ Γ1 t A -> SnNor S Δ Γ2 t[r] A
  | Typing.SnNor.lam h1 h2 h3 => by simp; sorry
  | .tlam h1 h2 => sorry
  | .neu h1 => SnNor.neu (Typing.SnNeu.rename m h1)
  | .red h2 h3  => SnNor.red (SnRed.rename m h2) (.rename m h3)

  theorem Typing.SnNeu.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnNeu S Δ Γ1 t A -> SnNeu S Δ Γ2 t[r] A := sorry

  theorem Typing.SnRed.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnRed S Δ Γ1 t t' A -> SnRed S Δ Γ2 t[r] t'[r] A
  | .beta h1 h2 => sorry
  | .tbeta h1 h2 h3 => sorry
  | .app h1 h2 h3 => sorry
  | .tapp h1 h2 h3 h4 => sorry
end

@[simp]
instance : Model LR where
A A B := fun
  | Δ, Γ, λ[_] t => ∀ a, Typing.SnNor' A Δ Γ a -> Typing.SnNor' B Δ Γ t[su a::+0]
  | _, _, _ => False
Q P := fun
  | Δ, Γ, Λ[_] t => ∀ A a, Typing.SnNor' (P A) Δ Γ t[su a::+0]
  | _, _, _ => False


def KSetcons : KSet -> (Nat -> KSet) -> (Nat -> KSet)
| K, _, 0 => K
| _, ξ, n + 1 => ξ n

@[simp]
def LRcons : LR -> (Nat -> LR) -> (Nat -> LR)
| L, _, 0 => L
| _, ξ, n + 1 => ξ n

@[simp]
def LR.int_term (v : Nat -> LR) : Ty -> LR
| t#x => v x
| A -:> B => fun
  | Δ, Γ, λ[_] t => ∀ a, Typing.SnNor (int_term v A) Δ Γ a A -> Typing.SnNor (int_term v B) Δ Γ t[su a::+0] B --A B
  | _, _, _ => False
| ∀[_] P => fun
  | Δ, Γ, Λ[_] t => ∀ A a P', Typing.SnNor (int_term (LRcons A v) P) Δ Γ t[su a::+0:Ty] P' --P[su a ::+0] this is a problem now
  | _, _, _ => False

@[simp]
def LR.int_subst (v : Nat -> LR) (σ : Subst Ty) : Nat -> LR
| i => LR.int_term v (σ.act i)

@[simp]
def 𝒱' (A : Ty) (ξ : Nat -> LR) := LR.int_term ξ A

@[simp]
def 𝒱'' (A : Ty) (ξ : Nat -> LR) := ⟦ A ⟧ ξ

--this is where I'm sure. I don't know where to put the typing information
def ℰ Δ Γ A ξ := λ t:Term => ((Δ&Γ ⊢ t : A) ∧ Typing.SnNor' (𝒱'' A ξ) Δ Γ t)

@[simp]
def 𝒱 : (A : Ty) -> (Nat -> KSet) -> (Δ : List Kind) -> (Γ : List Ty) -> (t : Term) ->  Prop
| A -:> B, ξ, Δ, Γ, λ[_] t => ∀ {a}, Typing.SnNor (𝒱 A ξ) Δ Γ a A -> Typing.SnNor (𝒱 B ξ) Δ Γ t[su a::+0] B
| ∀[K] P, ξ, Δ, Γ, Λ[_] t  => ∀ {a : Ty}, Kinding.SnNor (𝒱ₖ K) Δ a K -> Typing.SnNor (𝒱 P (KSetcons (Kinding.SnNor (𝒱ₖ K)) ξ)) Δ Γ t[su a::+0:Ty] P[su a::+0:Ty] --added
--| t#x, ξ, Δ, _, _ => ξ x Δ (t#x) ★ disgusting
| _, _, _, _, _ => False

structure Typing.SemSubst (Δ : List Kind) (Γ1 Γ2 : List Ty) (σ : Subst Term) (ξ : (Nat -> KSet)) where
  act : ∀ {i T}, Γ1[i]? = some T -> (SnNor (𝒱 T ξ) Δ Γ2 (σ.act i) T)

structure Typing.SemSubst' (Δ : List Kind) (Γ1 Γ2 : List Ty) (σ : Subst Term) where
  act : ∀ {i T}, Γ1[i]? = some T -> (SnNor (𝒱' T ξ) Δ Γ2 (σ.act i) T)

structure Typing.SemSubst'' (Δ : List Kind) (Γ1 Γ2 : List Ty) (σ : Subst Term) where
  act : ∀ {i T}, Γ1[i]? = some T -> ℰ Δ Γ2 T ξ (σ.act i) --(SnNor' (𝒱'' T ξ) Δ Γ2 (σ.act i))

notation:160 Δ:170 " ⊢ " Γ1:170 " -⟦" σ ";" ξ "⟧> " Γ2:170 => Typing.SemSubst Δ Γ1 Γ2 σ ξ

notation:160 Δ:170 " ⊢ " Γ1:170 " -⟦" σ "⟧> " Γ2:170 => Typing.SemSubst' Δ Γ1 Γ2 σ

notation:160 Δ:170 " ⊢' " Γ1:170 " -⟦" σ "⟧> " Γ2:170 => Typing.SemSubst'' Δ Γ1 Γ2 σ

-- theorem Typing.arrow_congr1 : Δ ⊢ₖ A' : ★ -> A =t= A' -> Δ&Γ ⊢ t : (A -:> B) -> Δ&Γ ⊢ t : (A' -:> B)
-- | h, j1, j2 =>
--   let lem := regularity j2=
--   match lem with
--   | Kinding.arrow _ h2 => .conv j2 (test j1) (Kinding.arrow h h2)

mutual
  theorem Typing.SnNor.soundness : SnNor S Δ Γ t A -> Δ&Γ ⊢ t : A
  | .lam _ h4 h5 => Typing.lam h5 (Typing.SnNor.soundness h4)
  | .tlam h1 h2 => Typing.tlam (Typing.SnNor.soundness h2)
  | .neu h2 => Typing.SnNeu.soundness h2
  | .red h2 h3 => SnRed.soundness h2 (SnNor.soundness h3)

  theorem Typing.SnNeu.soundness : SnNeu S Δ Γ t A -> Δ&Γ ⊢ t : A
  | .var h1 h3 => Typing.var h1 h3
  | .app h3 h4 => Typing.app (Typing.SnNeu.soundness h3) (Typing.SnNor.soundness h4)
  | .tapp h2 h3 h4 => Typing.tapp (Typing.SnNeu.soundness h2) (Kinding.SnNor.soundness h4) h3

  theorem Typing.SnRed.soundness : SnRed S Δ Γ t t' A -> Δ&Γ ⊢ t' : A -> Δ&Γ ⊢ t : A
  | .beta h2 h3, j1 => Typing.app h3 (SnNor.soundness h2)
  | .tbeta h2 h3 h4, j1 => Typing.tapp h3 h2 h4
  | .app h1 h2 h3, Typing.app j1 j2 =>
    let lem3 := SnRed.soundness h2 h3
    Typing.app lem3 h1
  | .tapp h1 h2 h3 h4, Typing.tapp _ j2 j3 => Typing.tapp (SnRed.soundness h2 h3) h1 h4
end

theorem Typing.SemSubst.id : Δ ⊢ X -⟦+0;ξ⟧> X := .mk @λ i T h1 => SnNor.neu (SnNeu.var h1 sorry)

theorem Typing.SemSubst.lift (m : Δ ⊢ Γ1 -⟦σ;ξ⟧> Γ2) A : Δ ⊢ (A::Γ1) -⟦σ.lift;ξ⟧> (A::Γ2) := .mk @λ i T h1 =>
  match i with
  | 0 => SnNor.neu (SnNeu.var h1 sorry)
  | n + 1 => by simp at *; sorry

theorem Typing.SemSubst.compose (m1 : Δ ⊢ Γ1 -⟦σ;ξ⟧> Γ2) (m2 : Γ2 -⟨r⟩> Γ3)
  : Δ ⊢ Γ1 -⟦σ ∘ r.to;ξ⟧> Γ3 := .mk @λ i T h1 => sorry

theorem Typing.SemSubst.hcompose :
  Δ1 ⊢ A -⟦σ;ξ⟧> B ->
  Δ1 -⟨r⟩> Δ2 ->
  Δ2 ⊢ A⟨r⟩ -⟦σ ◾ @r.to Ty;ξ⟧> B⟨r⟩
:= sorry

theorem Typing.SemSubst'.hcompose :
  Δ1 ⊢ A -⟦σ⟧> B ->
  Δ1 -⟨r⟩> Δ2 ->
  Δ2 ⊢ A⟨r⟩ -⟦σ ◾ @r.to Ty⟧> B⟨r⟩
:= sorry

theorem Typing.SemSubst.su (j : SnNor (𝒱 A ξ) Δ Γ a A) (m : Δ ⊢ Γ1 -⟦σ;ξ⟧> Γ2) : Δ ⊢ (A::Γ1) -⟦su a::σ;ξ⟧> Γ2 := SemSubst.mk @ λ i _ h =>
  sorry

@[simp]
def SemanticTyping (Δ : List Kind) (Γ1 : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ Γ2 ξ}, Δ ⊢ Γ1 -⟦σ;ξ⟧> Γ2 -> Typing.SnNor (𝒱 A ξ) Δ Γ2 t[σ] A

@[simp]
def SemanticTyping' (Δ : List Kind) (Γ1 : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ Γ2 ξ}, Δ ⊢ Γ1 -⟦σ⟧> Γ2 -> Typing.SnNor (𝒱' A ξ) Δ Γ2 t[σ] A

@[simp]
def SemanticTyping'' (Δ : List Kind) (Γ1 : List Ty) (t : Term) (A : Ty) :=
  --∀ {σ Γ2 ξ}, Δ ⊢' Γ1 -⟦σ⟧> Γ2 -> ℰ Δ Γ2 A ξ t[σ] this was the first attempt·
  ∀ {σ Γ2 ξ}, Δ ⊢' Γ1 -⟦σ⟧> Γ2 -> ℰ Δ Γ2 A ξ t[σ]

notation:170 Δ:170 "&" Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Δ Γ t A

notation:170 Δ:170 "&" Γ:170 " ⊨' " t:170 " : " A:170 => SemanticTyping' Δ Γ t A
--theorem LR.rename {A : Ty} {ξ : Nat -> LR} (r : Ren) : LR.int_term ξ A[r] = LR.int_term (ξ ∘ r) A := by sorry

notation:170 Δ:170 "&" Γ:170 " ⊨'' " t:170 " : " A:170 => SemanticTyping'' Δ Γ t A

theorem LR.yourdad : T = (σ.act n) ->
int_term (LRcons A ξ) (Ty.from_action ((σ ∘ +1).act n)) Δ Γ =
int_term ξ T Δ Γ := by
  intro eq
  fun_induction int_term ξ T
  case _ =>
    simp [Subst.compose]
    generalize zdef : σ.act n = z at *
    cases z; simp_all
    cases eq; simp
  case _ =>
    simp [Subst.compose]

    sorry
  case _ =>
    sorry

theorem LR.ricky : (LRcons A (int_subst ξ σ)) = int_subst (LRcons A ξ) (re 0 :: σ ∘ +1) := by
  funext n
  cases n
  case _ =>
    simp
  case _ =>
    simp
    funext Δ Γ
    rw [yourdad]
    rfl

theorem LR.kartik : (LRcons A_1 (int_subst (LRcons A ξ) (re 0 :: σ ∘ +1))) = int_subst (LRcons A_1 (LRcons A ξ )) (re 0 :: re 1 :: σ ∘ +1 ∘ +1) := by
  rw [ricky]; simp

theorem LR.andrew_marmaduke : (int_term (LRcons A ξ) P[re 0 :: σ ∘ +1:_]) = (int_term (int_subst (LRcons A ξ) (re 0 :: σ ∘ +1)) P) := by
  induction P generalizing σ ξ A
  case _ =>
    simp
  case _ ih =>
    simp
    funext x1 x2 x3
    cases x3; simp; simp; simp; simp; simp; apply Iff.intro; intro h A1 a P'; rw [kartik]; replace ih := @ih A1 (LRcons A ξ) (re 0 :: σ ∘ +1); simp at ih; rw [<-ih]; apply h
    intro h A1 a P'; replace h := @h A1; rw [kartik] at h; replace ih := @ih A1 (LRcons A ξ) (re 0 :: σ ∘ +1); simp at ih; rw [<-ih] at h; apply h
  case _ ih1 ih2 =>
    simp
    funext x1 x2 x3
    cases x3; simp; simp; simp; apply Iff.intro; intro h a j; rw [<-ih2]; apply h; rw [ih1]; apply j; intro h A' B' a j; rw [ih2]; apply h; rw [<-ih1]; apply j
    simp; simp

theorem LR.yourmom :
∀ A (ξ : Nat -> LR) (σ : Subst Ty), (int_subst (LRcons A ξ) (re 0 :: σ ∘ +1)) =
(LRcons A (int_subst ξ σ)) := by
  intro A ξ σ
  funext n Δ Γ
  cases n
  case _ =>
    simp
  case _ n =>
    simp

    funext x
    rw [LR.yourdad]; rfl

-- SnNor (int_term ξ A[σ]) Δ' Γ[σ] t A[σ] = SnNor (int_term (LR.int_subst ξ σ) A) Δ Γ t A

theorem LR.subst : ∀ (A : Ty) (σ : Subst Ty) (ξ : Nat -> LR),
  int_term ξ A[σ] = int_term (int_subst ξ σ) A
| A -:> B, σ, ξ => by
  simp
  funext x1 x2 x3
  congr
  funext
  have lemA := LR.subst A σ ξ
  have lemB := LR.subst B σ ξ
  rw [lemA]
  rw [lemB]
| ∀[_] P, σ, ξ => by
  simp
  funext x1 x2 x3
  congr
  funext x4 x5 x6 x7
  let lem := LR.subst P (re 0:: σ ∘ +1:_)
  have lem2 : (∀ (A : LR) (a P' : Ty), Typing.SnNor (int_term (LRcons A ξ) P[re 0 :: σ ∘ +1:_]) x4 x5 x7[su a :: +0:_] P') =
              (∀ (A : LR) (a P' : Ty), Typing.SnNor (int_term (int_subst (LRcons A ξ) (re 0 :: σ ∘ +1)) P) x4 x5 x7[su a :: +0:_] P')
  := by ext; apply Iff.intro; intro h A a P'; rw [<-andrew_marmaduke]; apply h; intro h A a P'; rw [andrew_marmaduke]; apply h
  rw [lem2]
  have lem3 : ∀ A, (int_term (int_subst (LRcons A ξ) (re 0 :: σ ∘ +1)) P) = (int_term (LRcons A (int_subst ξ σ)) P) := by
    intro A
    rw [yourmom]
  ext; apply Iff.intro; intro h A a P'; rw [<-lem3]; apply h; intro h A a P'; rw [lem3]; apply h
| t#x, σ, ξ => by simp

theorem beta : 𝒱' (A[su t::+0]) ξ = 𝒱' A (LRcons (𝒱' t ξ) ξ) :=
by
  simp
  rw [LR.subst]
  congr
  funext x1 x2 x3
  cases x1
  case _ => simp
  case _ => simp

--the '' denotes the use of model
theorem beta'' : 𝒱'' (A[su t::+0]) ξ = 𝒱'' A ((𝒱'' t ξ) :: ξ) :=
by
  simp
  congr
  funext n
  cases n
  case _ =>
    simp
  case _ =>
    simp

theorem test' :
  Typing.SnNor (𝒱' P (LRcons (𝒱' a ξ) ξ)) Δ Γ t A ->
  Typing.SnNor (𝒱' P[su a ::+0] ξ) Δ Γ t A
| j => by simp at *; rw [<-beta] at j; simp at j; apply j

theorem test :
  Kinding.SnNor (𝒱ₖ K) Δ a K ->
  Typing.SnNor (𝒱 P (KSetcons (Kinding.SnNor (𝒱ₖ K)) ξ)) Δ Γ t A ->
  Typing.SnNor (𝒱 P[su a :: +0] ξ) Δ Γ t A
:= by sorry

theorem test'' :
  Typing.SnNor' (𝒱'' P ((𝒱'' a ξ ) :: ξ )) Δ Γ t ->
  Typing.SnNor' (𝒱'' P[su a :: +0] ξ) Δ Γ t
:= by intro j; rw [beta'']; apply j

theorem SemanticTyping.tapp'' :
  V = 𝒱'' (∀[K] P) ξ ->
  T = (∀[K] P) ->
  Δ&Γ ⊢ f : T ->
  Typing.SnNor' V Δ Γ f ->
  Δ ⊢ₖ a : K ->
  Kinding.SnNor (𝒱ₖ K) Δ a K ->
  Typing.SnNor' (𝒱' P[su a :: +0] ξ) Δ Γ (f •[a])
| eq1, eq2, .tlam (t := t) j1, Typing.SnNor'.tlam (S2 := S2) h1 h2, j3, j4 => sorry
| eq1, eq2, j1, .red (S2 := S2) (t' := f') h2 h3, j3, j4 =>
  sorry
| eq1, eq2, j1, .neu h1, j3, j4 => Typing.SnNor'.neu (Typing.SnNeu'.tapp (P := P) h1 rfl j4)

theorem SemanticTyping.tapp' :
  V = 𝒱' (∀[K] P) ξ ->
  T = (∀[K] P) ->
  Δ&Γ ⊢ f : T ->
  Typing.SnNor V Δ Γ f T ->
  Δ ⊢ₖ a : K ->
  Kinding.SnNor (𝒱ₖ K) Δ a K ->
  Typing.SnNor (𝒱' P[su a :: +0] ξ) Δ Γ (f •[a]) P[su a ::+0]
| eq1, eq2, .tlam (t := t) j1, Typing.SnNor.tlam (S2 := S2) h1 h2, j3, j4 =>
  by
    injection eq2 with e1 e2
    simp only [ℛ] at h1
    symm at e1 e2
    subst eq1 e1 e2
    let h' : 𝒱' (∀[K]P) ξ Δ Γ (Λ[K]t)[.id] := h1 (TypingRen.id Γ)
    simp at h'
    replace h' := h' (𝒱' a ξ) a
    simp
    let lem := @test' P a ξ
    apply Typing.SnNor.red; apply Typing.SnRed.tbeta; apply j3; apply Typing.tlam;
    apply Typing.SnNor.soundness; apply h2; rfl; apply lem; apply h'; apply S2
| eq1, eq2, j1, .red (S2 := S2) (t' := f') h2 h3, j3, j4 =>
  by
    apply Typing.SnNor.red
    apply Typing.SnRed.tapp
    apply j3; rw [<-eq2] at *
    apply h2
    rw [<-eq2] at *; apply Typing.SnNor.soundness h3
    apply rfl
    apply SemanticTyping.tapp'
    apply eq1
    apply eq2
    apply Typing.SnNor.soundness h3; apply h3; apply j3; apply j4; apply S2
| eq1, eq2, j1, .neu h1, j3, j4 => Typing.SnNor.neu (Typing.SnNeu.tapp (h1 |> cast (by rw [<-eq2])) rfl j4)


theorem SemanticTyping.tapp :
  V = 𝒱 (∀[K] P) ξ ->
  T = (∀[K] P) ->
  Δ&Γ ⊢ f : T ->
  Typing.SnNor V Δ Γ f T ->
  Δ ⊢ₖ a : K ->
  Kinding.SnNor (𝒱ₖ K) Δ a K ->
  Typing.SnNor (𝒱 P[su a :: +0] ξ) Δ Γ (f •[a]) P[su a ::+0]
| eq1, eq2, .tlam (t := t) j1, Typing.SnNor.tlam (S2 := S2) h1 h2, j3, j4 =>
  by
    injection eq2 with e1 e2

    simp only [ℛ] at h1
    symm at e1 e2
    subst eq1 e1 e2
    let h' : 𝒱 (∀[K]P) ξ Δ Γ (Λ[K]t)[.id] := h1 (TypingRen.id Γ)
    simp at h'
    replace h' := @h' a j4 --(𝒱 P[su a ::+0:Ty])
    apply Typing.SnNor.red; apply Typing.SnRed.tbeta; apply j3; apply Typing.tlam j1; rfl; have lem := @test K Δ a P ξ Γ t[su a :: +0:_];
    apply lem; apply j4; apply h'; apply S2 --apply h'; apply 𝒱 P[su a :: +0]
| eq1, eq2, j1, .red (S2 := S2) (t' := f') h2 h3, j3, j4 =>
  by
    apply Typing.SnNor.red;
    apply Typing.SnRed.tapp;
    apply j3; rw [<-eq2] at *;
    apply h2;
    rw [<-eq2] at *; apply Typing.SnNor.soundness h3;
    apply rfl;
    apply SemanticTyping.tapp
    apply eq1;
    apply eq2;
    apply Typing.SnNor.soundness h3; apply h3; apply j3; apply j4; apply S2;
| eq1, eq2, j1, .neu h1, j3, j4 => Typing.SnNor.neu (Typing.SnNeu.tapp (h1 |> cast (by rw [<-eq2])) rfl j4)

theorem SemanticTyping.app' :
  S = 𝒱' (A -:> B) ξ ->
  T = A -:> B ->
  Typing.SnNor S Δ Γ f T ->
  Typing.SnNor (𝒱' A ξ) Δ Γ a A ->
  Typing.SnNor (𝒱' B ξ) Δ Γ (f • a) B
| eq1, eq2, Typing.SnNor.lam (t := t) (S2 := S2) h1 h2 h3, j2 =>
  let lem2 : (λ x => x) = @id Nat := by unfold id; rfl
  let lem : Typing.SnNor (𝒱' B ξ) Δ Γ t[su a :: +0] B := by
    subst eq1
    simp [ℛ] at h1
    replace h1 := h1 (TypingRen.id Γ) a j2
    apply h1
  have lem3 := Typing.SnNor.soundness h2
  by
    injection eq2 with e1 e2
    apply Typing.SnNor.red; apply Typing.SnRed.beta; subst e1; apply j2; subst e1; rw [e2] at lem3; apply Typing.lam h3 lem3; apply lem; apply S2
    --apply Typing.SnNor.red (Typing.SnRed.beta sorry (Typing.lam h3 (lem3))) lem
| eq1, eq2, .neu h, j2 => by subst eq1 eq2; apply Typing.SnNor.neu (Typing.SnNeu.app h j2)
| eq1, eq2, .red (S2 := S2) h1 h2, j2 =>
  have lem1 := SemanticTyping.app' eq1 eq2 h2 j2
  by
    apply Typing.SnNor.red; apply Typing.SnRed.app; apply Typing.SnNor.soundness j2; rw [eq2] at h1; apply h1; rw [eq2] at h2; apply Typing.SnNor.soundness h2; apply lem1; apply S2

theorem SemanticTyping.app :
  S = 𝒱 (A -:> B) ξ ->
  T = A -:> B ->
  Typing.SnNor S Δ Γ f T ->
  Typing.SnNor (𝒱 A ξ) Δ Γ a A ->
  Typing.SnNor (𝒱 B ξ) Δ Γ (f • a) B
| eq1, eq2, Typing.SnNor.lam (t := t) (S2 := S2) h1 h2 h3, j2 =>
  let lem2 : (λ x => x) = @id Nat := by unfold id; rfl
  let lem : Typing.SnNor (𝒱 B ξ) Δ Γ t[su a :: +0] B := by
    subst eq1
    simp [ℛ] at h1
    replace h1 := h1 (TypingRen.id Γ) j2
    apply h1
  have lem3 := Typing.SnNor.soundness h2
  by
    injection eq2 with e1 e2
    apply Typing.SnNor.red; apply Typing.SnRed.beta; subst e1; apply j2; subst e1; rw [e2] at lem3; apply Typing.lam h3 lem3; apply lem; apply S2
    --apply Typing.SnNor.red (Typing.SnRed.beta sorry (Typing.lam h3 (lem3))) lem
| eq1, eq2, .neu h, j2 => by subst eq1 eq2; apply Typing.SnNor.neu (Typing.SnNeu.app h j2)
| eq1, eq2, .red (S2 := S2) h1 h2, j2 =>
  have lem1 := SemanticTyping.app eq1 eq2 h2 j2
  by
    apply Typing.SnNor.red; apply Typing.SnRed.app; apply Typing.SnNor.soundness j2; rw [eq2] at h1; apply h1; rw [eq2] at h2; apply Typing.SnNor.soundness h2; apply lem1; apply S2

theorem Typing.fundamental'' : Δ&Γ ⊢ t : A -> Δ&Γ ⊨'' t : A
| var j1 j2, σ, Γ2, ξ, h => h.act j1
| lam (t := t) (A := A) (B := B) j1 j2, σ, Γ2, ξ, h => sorry
| app j1 j2, σ, Γ2, ξ, h => sorry
| tlam (K := K) j, σ, Γ2, ξ, h => sorry
| tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, Γ2, ξ, h => sorry

theorem Typing.fundamental : Δ&Γ ⊢ t : A -> Δ&Γ ⊨ t : A
| var j1 j2, σ, Γ2, ξ, h => h.act j1
| lam (t := t) (A := A) (B := B) j1 j2, σ, Γ2, ξ, h =>
  let j2' : Δ&(A::Γ) ⊨ t : B := fundamental j2
  sorry
  --let lem2 := j2' h
  -- have lem {Γ2' r'} : Γ2 -⟨r'⟩> Γ2' → 𝒱 (A -:> B) Δ Γ2' (λ[A]t[σ.lift][r'.to.lift]) := λ r a j2 =>
  --   j2' (SemSubst.su j2 (SemSubst.compose h r)) |> cast (by simp)
  -- SnNor.lam sorry sorry (t := t[σ.lift]) lem (j2' (SemSubst.lift h A))
| app j1 j2, σ, Γ2, ξ, h =>
  let j1' := fundamental j1 h
  let j2' := fundamental j2 h
  SemanticTyping.app rfl rfl j1' j2'
| tlam (K := K) j, σ, Γ2, ξ, h =>
  let h' : (K :: Δ) ⊢ Γ⟨.add 1⟩ -⟦σ ◾ +1;ξ⟧> Γ2⟨.add 1⟩ := h.hcompose (Δ2 := K::Δ) .succ
  let j3' := j.fundamental h'
  .tlam sorry j3'
| tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, Γ2, ξ, h =>
  let lem := j1.fundamental h
  let lem2 := j2.fundamental Kinding.SemSubst.id
  by rw [e]; apply SemanticTyping.tapp; rfl; rfl; apply Typing.SnNor.soundness lem; apply lem; apply j2; simp at lem2; apply lem2

theorem Typing.fundamental' : Δ&Γ ⊢ t : A -> Δ&Γ ⊨' t : A
| var j1 j2, σ, Γ2, ξ, h => h.act j1
| lam (t := t) (A := A) (B := B) j1 j2, σ, Γ2, ξ, h =>
  let j2' : Δ&(A::Γ) ⊨ t : B := fundamental j2
  sorry
  --let lem2 := j2' h
  -- have lem {Γ2' r'} : Γ2 -⟨r'⟩> Γ2' → 𝒱 (A -:> B) Δ Γ2' (λ[A]t[σ.lift][r'.to.lift]) := λ r a j2 =>
  --   j2' (SemSubst.su j2 (SemSubst.compose h r)) |> cast (by simp)
  -- SnNor.lam sorry sorry (t := t[σ.lift]) lem (j2' (SemSubst.lift h A))
| app j1 j2, σ, Γ2, ξ, h =>
  let j1' := fundamental' j1 h
  let j2' := fundamental' j2 h
  SemanticTyping.app' rfl rfl j1' j2'
| tlam (K := K) j, σ, Γ2, ξ, h =>
  let h' : (K :: Δ) ⊢ Γ⟨.add 1⟩ -⟦σ ◾ +1⟧> Γ2⟨.add 1⟩ := h.hcompose (Δ2 := K::Δ) .succ
  let j3' := j.fundamental' (ξ := ξ) h'
  let lem := Typing.SnNor.soundness j3'
  let lem2 := Typing.tlam lem
  .tlam (by intro r Γ3 q3; simp; intro S T2; rw [Term.smap_promote]; simp; sorry) j3' --here's the problem with the universal quantifier P'
| tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, Γ2, ξ, h =>
  let lem := j1.fundamental' h
  let lem2 := j2.fundamental Kinding.SemSubst.id
  by
    rw [e]; apply SemanticTyping.tapp'; rfl; rfl; apply Typing.SnNor.soundness; apply lem; apply lem; apply j2; simp at lem2; apply lem2
-- theorem Typing.SnNeu.consistency_lemma :
--   Γ = [] ->
--   SnNeu T Δ Γ t A ->
--   Δ&Γ ⊢ t : X ->
--   False
-- | e, .var h, j => by grind
-- | e, .app fn an, (.app fj aj) => fn.consistency_lemma e fj
-- | e1, .tapp fn e2, (.tapp fj aj e3) => fn.consistency_lemma e1 fj
-- | e, tn, .conv tj cv Bj => tn.consistency_lemma e tj

-- theorem Typing.SnNor.consistency_lemma :
--   Γ = [] ->
--   C =t= (∀[★] t#0) ->
--   SnNor T Δ Γ t A ->
--   Δ&Γ ⊢ t : C ->
--   False
-- | e, cv, .tlam tn, (.tlam tj) => sorry
-- | e, cv1, .tlam tn, (.conv tj cv2 Bj) => sorry
-- | e, cv, .lam lr tn, tj => sorry
-- -- | e, .tlam (.neu tn), .tlam tj => tn.consistency_lemma (by simp [e]) tj
-- -- | e, .tlam (.red tr tn), .tlam tj => tn.consistency_lemma (by simp [e]) sorry
-- | e, cv, .neu tn, j3 => tn.consistency_lemma e j3
-- | e, cv, .red tr tn, j3 => tn.consistency_lemma e cv sorry

-- theorem Typing.consistency : ¬ (Δ&[] ⊢ t : (∀[★] t#0))
-- | j => SnNor.consistency_lemma rfl Conv.refl (j.fundamental $ SemSubst.id) (j |> cast (by simp))

end TwoSortHet
