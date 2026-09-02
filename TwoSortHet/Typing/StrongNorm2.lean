
import LeanSubst
import TwoSortHet.Typing
import TwoSortHet.Typing.Substitute
import TwoSortHet.Kinding.StrongNorm
import TwoSortHet.Kinding.Value
import TwoSortHet.Reduction
import TwoSortHet.Model
open LeanSubst

namespace TwoSortHet
--naively following lean-sysf/OneSortHomArityGen/StrongNorm2.lean
def SnModelSet := Term -> Prop
def SnRedModelSet := Term -> Term -> Prop

def ℛ (S : SnModelSet) : SnModelSet
| t => ∀ {r: Ren}, S t[r]

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
    P' = P[su a::+0] ->
    --Kinding.SnNor S2 Δ a K ->
    SnNeu S3 (f •[a])

  inductive SnRed : SnModelSet -> SnRedModelSet
  | beta :
    SnNor S1 t ->
    --Δ&Γ ⊢ (λ[A]b) : (A -:> B) ->
    SnRed S2 ((λ[A] b) • t) b[su t::+0]
  | tbeta :
    --Δ ⊢ₖ t : K ->
    --Δ&Γ ⊢ (Λ[K] b) : (∀[K] P) ->
    P' = P[su t::+0] ->
    SnRed S ((Λ[K] b) •[t]) b[su t::+0:Ty]
  | app :
    --Δ&Γ ⊢ a : A ->
    SnRed S1 f f' ->
    --Δ&Γ ⊢ f' : (A -:> B) ->
    SnRed S2 (f • a) (f' • a)
  | tapp :
    --Δ ⊢ₖ a : K ->
    SnRed S1 f f' ->
    --Δ&Γ ⊢ f' : (∀[K] P) ->
    P' = P[su a::+0] ->
    SnRed S2 (f •[a]) (f' •[a])
end

@[simp]
instance : Model SnModelSet where
A A B := fun
  | λ[_] t => ∀ a, SnNor A a -> SnNor B t[su a::+0]
  | _ => False
Q P := fun
  | Λ[_] t => ∀ (A : SnModelSet) (a:Ty), SnNor (P A) t[su a::+0:Ty]
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

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
∀ σ ξ, 𝒞 Γ ξ σ -> ℰ A ξ t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

namespace SnNor
  theorem sound : SnNor A t -> SN Red t := by sorry

  theorem var x : SnNor A #x := SnNor.neu SnNeu.var

  mutual
    theorem SnNor.rename (r : Ren) : SnNor A t -> SnNor A t[r]
    | .lam (S2 := S2) h1 h2 =>
      let j := SnNor.rename r.lift h2
      SnNor.lam (S2 := S2) (by simp [ℛ] at *; rw [Term.smap_promote]; intro r'; simp; replace h1 := @h1 (r ∘ r'); simp at h1; apply h1) (by rw [Term.smap_promote]; rw [<-Ren.to_lift]; apply j)
    | .tlam (S2 := S2) h1 h2 =>
      let j := SnNor.rename r h2
      SnNor.tlam (S2 := S2) (by simp; simp [ℛ] at *; rw [Term.smap_promote]; intro r'; simp; replace h1 := @h1 (r ∘ r'); apply h1) (by rw [Term.smap_promote]; apply j)
    | .neu h1 => SnNor.neu (SnNeu.rename r h1)
    | .red h1 h2 =>
      let h2' := SnNor.rename r h2
      let h1' := SnRed.rename r h1
      SnNor.red h1' h2'

    theorem SnNeu.rename (r : Ren) : SnNeu A t -> SnNeu A t[r]
    | .var (x := x) => .var
    | .app h1 h2 =>
      let h1' := SnNeu.rename r h1
      let h2' := SnNor.rename r h2
      SnNeu.app h1' h2'
    | .tapp h1 h2 =>
      let h1' := SnNeu.rename r h1
      SnNeu.tapp h1' h2

    theorem SnRed.rename (r : Ren) : SnRed A t t' -> SnRed A t[r] t'[r]
    | .beta (S1 := S1) (S2 := S2) (t := t) (A := A) (b := b) h1 =>
      let h1' := SnNor.rename r h1
      let lem := @SnRed.beta S1 t[Ren.to r] S2 A b[re 0 :: r ∘ +1]
      by simp at *; simp at lem; apply lem; apply h1'
    | .tbeta (P := P) (P' := P') (K := K) (b := b) (t := t) (S := S) h1 =>
      let lem := SnRed.tbeta (b := b[Ren.to r]) (K := K) (S := S) (P := P) (t := t) (P' := P')
      by simp at *; simp at lem; apply lem; apply h1
    | .app h1 =>
      let h1' := SnRed.rename r h1
      SnRed.app h1'
    | .tapp h1 h2 =>
      let h1' := SnRed.rename r h1
      SnRed.tapp h1' h2

  end
end SnNor

-- namespace ℛ
--   @[simp]
--   theorem lam
--     : ℛ (𝒱 (A -:> B) ξ) (λ[C] b) <-> ∀ (r:Ren) a, ℰ A ξ a -> ℰ B ξ b[su a ::r]
--   := ⟨λ h1 r a h2 =>
--       let h1 := @h1 r
--       let h1 := h1 a h2
--       by simp at *; sorry,
--       sorry⟩

-- end ℛ

namespace ℰ
  theorem weaken : ℰ (A[+1]) (B::ξ) = ℰ A ξ := by simp [ℰ]; congr 1

  theorem beta : ℰ (A[su t::+0]) ξ = ℰ A (𝒱 t ξ :: ξ) :=
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

  theorem rename (r : Ren) : ℰ A (ξ ∘ r.act) t = ℰ A[r] ξ t := by simp only [ℰ, 𝒱] at *; congr 1; rw [Model.rename]
end ℰ

namespace 𝒞
  theorem re :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (re x ::σ)
  := by
    intro h; simp only [𝒞]; intro i
    cases i <;> simp
    case _ =>
      apply SnNor.neu SnNeu.var
    case _ n =>
      intro A j
      replace h := h n A j
      let lem := ℰ.weaken (A := A) (B := S) (ξ := ξ)
      simp [𝒞] at h
      let lem1 := @ℰ.weaken
      have yourmom : SnNor (⟦A⟧ ξ) = ℰ A ξ := by simp

      sorry

  theorem rename : 𝒞 Γ ξ σ -> 𝒞 Γ ξ (σ ∘ (Ren.to r)) := by
    intro h; simp [𝒞, ℰ] at *; intro i A j
    replace h := h i A j
    let lem := SnNor.SnNor.rename r h
    simp at lem
    apply lem

  theorem lift :
    𝒞 Γ ξ σ ->
    𝒞 (A::Γ) (S::ξ) (.re 0::σ ∘ +1)
  := by
    intro h; apply re; apply rename h
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
      simp [ℛ] at j1; replace j1 := @j1 .id; simp [Model.A] at j1; replace j1 := j1 a h2;
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
      replace j1 := @j1 .id
      simp [Model.A] at j1

  theorem tapp :
    S = 𝒱 (∀[K] P) ξ ->
    SnNor S f ->
    ℰ (P[su a::+0]) ξ (f •[a])
  | eq, SnNor.lam j1 j2 => by subst eq; simp [ℛ] at j1; replace j1 := @j1 .id; simp [Model.Q] at j1
  | eq, SnNor.neu j1 => SnNor.neu (SnNeu.tapp (P := P) j1 rfl)
  | eq, SnNor.red j1 j2 =>
    let lem1 := SnRed.tapp (S2 := ⟦∀[K]P⟧ ξ) (P := P) (a := a) j1 rfl
    let lem2 := tapp (a := a) eq j2
    SnNor.red lem1 lem2
  | eq, SnNor.tlam (S2 := S2) j1 j2 =>
    by
      simp [ℰ] at *
      simp [ℛ] at j1
      subst eq
      replace j1 := @j1 .id
      simp [Model.Q] at j1
      apply SnNor.red
      apply SnRed.tbeta
      apply rfl
      apply a
      let lem := @beta a P ξ
      simp at lem
      rw [lem]
      replace j1 := j1 (⟦a⟧ ξ)
      apply j1
      apply S2

  --------------------------------------------------------------------------
  --i need this
  --------------------------------------------------------------------------

  -- inserts variable #s at position n in term t
  def insert : Nat -> Nat -> Term -> Term := λ s n t =>
  match t with
  | Term.var m => if m = n then #s else Term.var m
  | Term.app f a => Term.app (insert s n f) (insert s n a)
  | Term.lam A b => Term.lam A (insert (s + 1) (n + 1) b)
  | Term.tapp f a => Term.tapp (insert s n f) a
  | Term.tlam K a => Term.tlam K (insert s n a)

  theorem insert_id : insert k k t = t :=
  by
    induction t generalizing k
    case _ n =>
      unfold insert
      split
      case _ h =>
        rw [h]
      case _ =>
        rfl
    case _ ih1 ih2 =>
      unfold insert
      simp_all
    case _ ih =>
      unfold insert
      congr
      replace ih := @ih (k + 1)
      rw [ih]
    case _ ih =>
      unfold insert
      simp
      apply ih
    case _ ih =>
      unfold insert
      congr
      apply ih

  theorem insert_id_smap : insert k k = Term.smap +0 := by
    funext b
    simp [Term.smap_promote]
    apply insert_id

  theorem ty_smap_id : ((su #0 :: +1).lift k ◾ (@Subst.succ Ty)) = (su #0 :: +1).lift k :=
  by
    unfold Subst.hcompose
    simp_all
    generalize zdef : (su #0 :: +1).lift k = z
    cases z
    simp_all
    funext n
    unfold Subst.cons at zdef
    unfold Subst.lift at zdef
    injection zdef with f
    rw [<-f]
    simp
    split
    case _ heq =>
      split at heq
      case _ =>
        simp at heq
      case _ h1 =>
        split at heq
        case _ heq2 =>
          split at heq2
          case _  heq3 =>
            injection heq2 with j
            rw [<-j] at heq
            simp at heq
            rw [<-heq]
            simp
            rw [<-j]
            simp
            grind
          case _ heq3 =>
            simp at heq2
        case _ heq2 =>
          split at heq2
          case _ =>
            simp at heq2
          case _ =>
            simp at heq
    case _ heq =>
      rw [heq]

  theorem lift_k_insert_eq : insert k k = Term.smap ((su #0 :: +1).lift k) :=
  by
    funext b
    induction b generalizing k
    case _ n =>
      unfold insert
      split
      case _ h =>
        subst h
        unfold Term.smap
        unfold Subst.lift
        simp
        unfold Ren.add
        simp
      case _ h =>
        unfold Term.smap
        unfold Subst.lift
        cases Nat.decLt n k
        case _ j =>
          simp
          split
          case _ =>
            simp
          case _ h2 =>
            split
            case _ heq =>
              unfold Subst.cons at heq
              simp at heq
              split at heq
              case _ heq2 =>
                grind
              case _ heq2 =>
                simp at heq
            case _ heq =>
              unfold Subst.cons at heq
              simp at heq
              split at heq
              case _ =>
                simp at heq
              case _ n' n'' heq2 =>
                injection heq with eq
                have lem : n'' + 1 = n''.succ := by simp
                rw [<-lem] at heq2
                rw [<-eq]
                simp
                grind
        case _ j =>
          simp_all
    case _ ih1 ih2 =>
      unfold insert
      simp
      apply And.intro; apply ih1; apply ih2
    case _ ih =>
      simp
      unfold insert
      congr
      replace ih := @ih (k + 1)
      simp [Subst.rewrite_lift_succ] at ih
      simp at ih
      apply ih
    case _ ih =>
      unfold insert
      simp
      apply ih
    case _ ih =>
      unfold insert
      simp
      rw [ty_smap_id]
      apply ih

  theorem su_to_id : Term.smap (su #0 :: +1) = Term.smap +0 :=
  by
    let lem1 := @insert_id_smap 0
    let lem2 := @lift_k_insert_eq 0
    simp at lem2
    rw [<-lem2]
    rw [<-lem1]

  --------------------------------------------------------------------------
  -- done
  --------------------------------------------------------------------------

  theorem lam :
    ℛ (𝒱 (A -:> B) ξ) (λ[C] b) ->
    ℰ (A -:> B) ξ (λ[C] b)
  := by
      intro h
      apply SnNor.lam; apply h
      simp [ℛ] at h; simp [Model.A] at h
      replace h := @h (Ren.add 1) #0
      simp at h
      have lem := @Term.smap_promote (su #0 :: +1) b
      simp at lem
      rw [<-lem] at h
      rw [su_to_id] at h
      rw [Term.smap_promote] at h
      simp at h
      apply h
      apply SnNor.neu (SnNeu.var)

  theorem tlam :
    ℛ (𝒱 (∀[K]P) ξ) (Λ[K]b) ->
    ℰ (∀[K]P) ξ (Λ[K]b)
  := by
    intro h
    simp at *
    sorry

end ℰ

theorem fundamental {Γ : List Ty} : Δ&Γ ⊢ t : A -> Γ ⊨ t : A
| .var (x := x) j1 j2, σ, ξ, h => h x A j1
| .lam (t := t) (A := A) (B := B) j1 j2, σ, ξ, h =>
  let j2' := fundamental j2
  by
    apply ℰ.lam; simp [Model.A]; simp [ℛ]; simp at j2'
    intro r a h2
    rw [Term.smap_promote]
    simp
    apply j2'
    intro i A' h'
    cases i <;> simp at *; subst h'; exact h2
    case _ n =>
    replace h := h _ _ h'
    replace h := SnNor.SnNor.rename r h
    simp at h
    exact h
| .app j1 j2, σ, ξ, h =>
  let j1' := fundamental j1 σ ξ h
  let j2' := fundamental j2 σ ξ h
  ℰ.app rfl j1' j2'
| .tlam (K := K) (P := P) j, σ, ξ, h =>
  let j' := fundamental j
  by
    apply ℰ.tlam; simp [Model.Q]; simp [ℛ]; simp at j'
    intro r A a
    rw [Term.smap_promote]
    simp
    replace h := 𝒞.lift (S := A) (A := a) h
    simp [𝒞] at h
    sorry
| .tapp (a := a) (f := f) (K := K) (P := P) j1 j2 e, σ, ξ, h =>
  let j1' := fundamental j1 σ ξ h
  by subst e; apply ℰ.tapp rfl j1'
