import LeanSubst
import OneSortHomArityGen.Typing

open LeanSubst

def Term.beq : Term -> Term -> Bool
| var x, var y => x = y
| ctor .star _, ctor .star _ => true
| ctor .arr ts1, ctor .arr ts2 =>
  Term.beq (ts1 0) (ts2 0) && Term.beq (ts1 1) (ts2 1)
| ctor .app ts1, ctor .app ts2 =>
  Term.beq (ts1 0) (ts2 0) && Term.beq (ts1 1) (ts2 1)
| ctor .tapp ts1, ctor .tapp ts2 =>
  Term.beq (ts1 0) (ts2 0) && Term.beq (ts1 1) (ts2 1)
| bind .lam ts1 t1, bind .lam ts2 t2 =>
  Term.beq (ts1 0) (ts2 0) && Term.beq t1 t2
| bind .tlam _ t1, bind .tlam _ t2 => Term.beq t1 t2
| bind .all _ t1, bind .all _ t2 => Term.beq t1 t2
| _, _ => false

instance : BEq Term where
  beq := Term.beq

instance : LawfulBEq Term where
  rfl := by {
    intro a; induction a
    case var => simp [BEq.beq, Term.beq]
    case bind v _ _ _ _ =>
      cases v <;> simp [BEq.beq, Term.beq] at * <;> simp [*]
    case ctor v _ _ =>
      cases v <;> simp [BEq.beq, Term.beq] at * <;> simp [*]
  }
  eq_of_beq := by {
    intro a b h
    simp [BEq.beq] at h
    fun_induction Term.beq <;> simp at *
    case _ => exact h
    case _ ih1 ih2 => rw [ih1 h.1, ih2 h.2]; simp
    case _ ih1 ih2 => rw [ih1 h.1, ih2 h.2]; simp
    case _ ih1 ih2 => rw [ih1 h.1, ih2 h.2]; simp
    case _ ih1 ih2 => rw [ih1 h.1, ih2 h.2]; simp
    case _ ih => rw [ih h]
    case _ ih => rw [ih h]
  }

def Term.is_type (Γ : Ctx Term) : Term -> Bool
| var x =>
  match Γ[x] with
  | ctor .star _ => true
  | _ => false
| ctor .arr ts => (ts 0).is_type Γ && (ts 1).is_type Γ
| bind .all _ t => t.is_type (★::Γ)
| _ => false

theorem is_type_sound : A.is_type Γ -> Γ ⊢ A type := by
  intro h; fun_induction Term.is_type
  case _ t ih =>
    apply Kinding.var; simp at *
    apply ih
  case _ h => cases h
  case _ ts ih1 ih2 =>
    simp at h; rcases h with ⟨h1, h2⟩
    rw [<-Vec.eta2 ts]; apply Kinding.arr
    apply ih1 h1; apply ih2 h2
  case _ ts t ih =>
    simp; apply Kinding.all
    apply ih h
  case _ => cases h

def Term.is_all : Term -> Option Term
| bind .all _ t => t
| _ => none

def Term.is_arr : Term -> Option (Term × Term)
| ctor .arr ts => (ts 0, ts 1)
| _ => none

def Term.pred (ℓ : Nat) : Term -> Option Term
| var x => if x > ℓ then var (x - 1) else none
| ctor .star ts => ctor .star ts
| ctor .arr ts => do
  let A <- Term.pred ℓ (ts 0)
  let B <- Term.pred ℓ (ts 1)
  ctor .arr v[A, B]
| ctor .app ts => do
  let A <- Term.pred ℓ (ts 0)
  let B <- Term.pred ℓ (ts 1)
  ctor .arr v[A, B]
| ctor .tapp ts => do
  let A <- Term.pred ℓ (ts 0)
  let B <- Term.pred ℓ (ts 1)
  ctor .arr v[A, B]
| bind .all ts t => do
  let P <- Term.pred (ℓ + 1) t
  bind .all ts P
| bind .lam ts t => do
  let A <- Term.pred ℓ (ts 0)
  let b <- Term.pred (ℓ + 1) t
  bind .lam v[A] b
| bind .tlam ts t => do
  let b <- Term.pred (ℓ + 1) t
  bind .all ts b

def infer (Γ : Ctx Term) : Term -> Option Term
| .var x =>
  let A := Γ[x]
  if A.is_type Γ then A else none
| .ctor .app ts => do
  let f := ts 0
  let a := ts 1
  let F <- infer Γ f
  let A' <- infer Γ a
  let (A, B) <- F.is_arr
  if A' == A then B
  else none
| .ctor .tapp ts => do
  let f := ts 0
  let a := ts 1
  let F <- infer Γ f
  let P <- F.is_all
  if a.is_type Γ then P[su a::+0]
  else none
| .bind .lam ts t => do
  let A := ts 0
  let B <- infer (A::Γ) t
  let B <- Term.pred 0 B
  if A.is_type Γ then A -:> B
  else none
| .bind .tlam ts t => do
  let P <- infer (★::Γ) t
  :∀ P
| _ => none

-- TODO: too lazy to prove this right now
-- How to do it: generalize to ℓ and an iterated lift of +1 by ℓ (similar to free vars stuff)
-- That gives you a strong enough inductive hypothesis to prove this for all ℓ
-- then the 0 case is an easy corollary
--
-- Might be bugs in Term.pred itself, but clearly it is a definable function
theorem Term.pred_sound : Term.pred 0 t = some p -> t = p[+1] := by
  sorry

theorem Term.is_all_some : Term.is_all t = some P -> t = :∀ P := by
  intro h
  cases t <;> simp [Term.is_all] at h
  case _ n v ts t =>
  cases v <;> simp at h; subst h; simp

theorem Term.is_arr_some : Term.is_arr t = some F -> ∃ A B, t = A -:> B ∧ F = (A, B) := by
  intro h
  cases t <;> simp [Term.is_arr] at h
  case _ n v ts =>
  cases v <;> simp at h; subst h
  exists ts 0; exists ts 1; simp

theorem infer_sound : infer Γ t = some A -> Γ ⊢ t : A := by
  intro h; fun_induction infer generalizing A
  case _ Γ x A' h2 =>
    subst A'; injection h with e; subst e
    apply Typing.var rfl
    apply is_type_sound h2
  case _ => cases h
  case _ Γ ts f a ih1 ih2 =>
    replace h := Option.bind_eq_some_iff.1 h
    rcases h with ⟨u1, h1, h2⟩
    replace h2 := Option.bind_eq_some_iff.1 h2
    rcases h2 with ⟨u2, h2, h3⟩
    replace h3 := Option.bind_eq_some_iff.1 h3
    rcases h3 with ⟨u3, h3, h4⟩
    simp at h4; rcases h4 with ⟨h4, h5⟩
    replace h3 := Term.is_arr_some h3
    rcases h3 with ⟨A', B, h3, h6⟩
    subst h4 h3 h6; simp at h5; subst h5
    rw [<-Vec.eta2 ts]; apply Typing.app
    apply ih1 h1
    apply ih2 h2
  case _ Γ ts f a ih =>
    replace h := Option.bind_eq_some_iff.1 h
    rcases h with ⟨u1, h1, h2⟩
    replace h2 := Option.bind_eq_some_iff.1 h2
    rcases h2 with ⟨u2, h2, h3⟩; simp at h3
    rcases h3 with ⟨h3, h4⟩
    replace h2 := Term.is_all_some h2; subst h2 h4
    rw [<-Vec.eta2 ts]; apply Typing.tapp
    apply ih h1
    apply is_type_sound h3
    simp [a]
  case _ Γ ts t A' ih =>
    simp at h
    replace h := Option.bind_eq_some_iff.1 h
    rcases h with ⟨u1, h1, h2⟩
    replace h2 := Option.bind_eq_some_iff.1 h2
    rcases h2 with ⟨u2, h2, h4⟩
    replace h2 := Term.pred_sound h2
    simp at h4; rcases h4 with ⟨h4, h5⟩; subst h2 h5
    rw [<-Vec.eta1 ts]; apply Typing.lam
    apply is_type_sound h4
    apply ih h1
  case _ Γ ts t ih =>
    replace h := Option.bind_eq_some_iff.1 h
    rcases h with ⟨u1, h1, h2⟩; simp
    injection h2 with e; subst e
    apply Typing.tlam
    apply ih h1
  case _ => cases h

def ex0 : Term := :∀ #0 -:> #0
def ex1 : Term := Λ :λ[#0] #0
def ex2 : Term := ex1 :@[ex0] :@ ex1

#eval infer Ctx.nil ex1
#eval infer Ctx.nil ex2
