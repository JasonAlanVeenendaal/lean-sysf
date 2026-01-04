
import LeanSubst

namespace OneSortHomArityGen

open LeanSubst

def Fin.cases1
  {motive : Fin 1 -> Prop}
  (h : motive 0)
  (v : Fin 1) : motive v
:= by
  induction v using Fin.induction; simp [*]
  case _ i _ => apply Fin.elim0 i

def Fin.cases2
  {motive : Fin 2 -> Prop}
  (h1 : motive 0) (h2 : motive 1)
  (v : Fin 2) : motive v
:= by
  induction v using Fin.induction; simp [*]
  case _ i h =>
    induction i using Fin.induction; simp [*]
    case _ i h => apply Fin.elim0 i

def Vec (T : Type u) (n : Nat) := Fin n -> T

def Vec.nil : Vec T 0 := λ x => nomatch x

def Vec.cons (t : T) (xs : Vec T n) : Vec T (n + 1)
| n => if h : n = 0 then t else xs (Fin.pred n h)

infixr:55 "::" => Vec.cons

def Vec.drop : Vec T (n + 1) -> Vec T n
| v => λ i => v (Fin.succ i)

def Vec.uncons :  Vec T (n + 1) -> T × Vec T n
| v => (v 0, drop v)

protected def Vec.reprPrec [Repr T] : {n : Nat} -> Vec T n -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let (h, t) := uncons v
  (repr h) ++ ", " ++ (Vec.reprPrec t i)

instance [Repr T] : Repr (Vec T n) where
  reprPrec v n := "v[" ++ Vec.reprPrec v n ++ "]"

syntax "v[" withoutPosition(term,*,?) "]"  : term

-- Adapted from Lean Prelude
macro_rules
| `(v[ $elems,* ]) => do
  let rec expandVecList (i : Nat) (result : Lean.TSyntax `term) : Lean.MacroM Lean.Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expandVecList i (<- ``(Vec.cons `$(⟨elems.getElems.get!Internal i⟩) $result))
  let size := elems.getElems.size
  expandVecList size (<- ``(Vec.nil))

-- Adapted from Lean Prelude
@[app_unexpander Vec.nil]
meta def unexpandVecNil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(v[])

-- Adapted from Lean Prelude
@[app_unexpander Vec.cons]
meta def unexpandVecCons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(v[])      => `(v[$x])
  | `(v[$xs,*]) => `(v[$x, $xs,*])
  | `(⋯)       => `(v[$x, $tail]) -- Unexpands to `[x, y, z, ⋯]` for `⋯ : List α`
  | _          => throw ()
| _ => throw ()

theorem Vec.nil_singleton (v1 v2 : Vec T 0) : v1 = v2 := by
  funext; case _ i =>
  cases i; case _ i p => cases p

@[simp]
theorem Vec.uncons_cons_cancel : uncons (h::t) = (h, t) := by
  simp [uncons, drop]; case _ n =>
  apply And.intro _ _
  case _ =>
    cases n <;> simp [cons]
  case _ =>
    funext; case _ i =>
    cases i; case _ i p =>
    cases i <;> simp [cons, Fin.pred]

@[simp]
theorem Vec.head_drop_cancel : v 0 :: drop v = v := by
  funext; case _ i =>
  cases i; case _ i p =>
  cases i <;> simp [cons, drop]

theorem Vec.cons_iff_uncons {t : Vec T n} : v = h::t <-> uncons v = (h, t) := by
  apply Iff.intro
  case _ => intro e; subst e; simp
  case _ =>
    intro e; simp [uncons] at e
    cases e; case _ e1 e2 =>
    subst e1; subst e2; simp

theorem Vec.cons_destruct (v : Vec T (n + 1)) : ∃ h t, v = cons h t := by
  generalize pdef : uncons v = p
  cases p; case _ h t =>
  exists h; exists t
  rw [cons_iff_uncons]; apply pdef

theorem Vec.induction
  {motive : {n : Nat} -> Vec T n -> Prop}
  (nc : motive Vec.nil)
  (cc : ∀ {n t} {v : Vec T n}, motive v -> motive (t::v))
  (v : Vec T n)
  : motive v
:= by
  induction n
  case _ => rw [nil_singleton v]; exact nc
  case _ n ih =>
    have lem := cons_destruct v
    rcases lem with ⟨h, t, e⟩; subst e
    apply cc; apply ih

-- theorem Vec.induction1
--   {motive : Vec T 1 -> Prop}
--   (h : ∀ {t : T}, motive v[t])

@[simp]
instance : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs i

@[simp]
theorem get_cons_head {t : Vec T n} : (h::t) 0 = h := by simp [Vec.cons]

@[simp]
theorem get_cons_tail_succ {t : Vec T n} : (h::t) (Fin.succ i) = t i := by
  simp [Vec.cons]; intro h; cases h

@[simp]
theorem get1_0 : v[a] 0 = a := by simp

@[simp]
theorem get2_0 : v[a, b] 0 = a := by simp

@[simp]
theorem get2_1 : v[a, b] 1 = b := by simp [Vec.cons]

def Vec.map (f : A -> B) (v : Vec A n) : Vec B n := λ i => f (v i)

@[simp]
theorem Vec.map_nil : Vec.map f v[] = v[] := by
  funext; case _ x => apply Fin.elim0 x

@[simp]
theorem Vec.map_cons : Vec.map f (h::t) = (f h)::Vec.map f t := by
  funext; case _ i =>
  cases i using Fin.cases <;> simp [Vec.map]

@[simp]
theorem Vec.eta0 (t : Vec T 0) : t = v[] := by apply Vec.nil_singleton

@[simp]
theorem Vec.eta1 (t : Vec T 1) : v[t 0] = t := by
  funext; case _ i =>
  cases i using Fin.cases1; simp

@[simp]
theorem Vec.eta2 (t : Vec T 2) : v[t 0, t 1] = t := by
  funext; case _ i =>
  cases i using Fin.cases2 <;> simp

@[simp]
theorem Vec.inv1 {a b : Vec T 1} : a = b <-> a 0 = b 0 := by
  apply Iff.intro; intro h; subst h; rfl
  intro h; funext; case _ i =>
  cases i using Fin.cases1; exact h

@[simp]
theorem Vec.inv2 {a b : Vec T 2} : a = b <-> a 0 = b 0 ∧ a 1 = b 1 := by
  apply Iff.intro; intro h; subst h; simp
  intro h; funext; case _ i =>
  cases i using Fin.cases2 <;> simp [*]

def Vec.update (i : Fin n) (t : T) (ts : Vec T n) : Vec T n
| x => if i = x then t else ts x

@[simp]
theorem Vec.update_eq : update i t ts i = t := by simp [update]

theorem Vec.update_neq : ∀ j ≠ i, update i t ts j = ts j := by
  simp [update]; intro j h1 h2
  exfalso; apply h1; rw [h2]

theorem Vec.update_stable i t {ts ts' : Vec T n} :
  (∀ j ≠ i, ts j = ts' j) ->
  ∀ j ≠ i, ts j = update i t ts' j
:= by
  intro h1 j h2; simp [update, *]
  intro h3; exfalso; apply h2; rw [h3]

def Vec.beq [BEq T] : {n : Nat} -> Vec T n -> Vec T n -> Bool
| 0, _, _ => true
| _ + 1, v1, v2 =>
  let (h1, t1) := Vec.uncons v1
  let (h2, t2) := Vec.uncons v2
  h1 == h2 && Vec.beq t1 t2

instance [BEq T] : BEq (Vec T n) where
  beq := Vec.beq

variable {S T : Type} [RenMap T] [SubstMap S T]

@[simp]
theorem Vec.subst_cons {t : Vec S n} {σ : Subst T}
  : ((h::t) i)[σ:T] = (h[σ:_]::map (·[σ:_]) t) i
:= by
  induction i using Fin.induction <;> simp at *
  case _ i ih =>
    cases n; apply Fin.elim0 i
    case _ n =>
    cases i using Fin.cases <;> simp [Vec.map] at *

-- @[simp]
-- theorem Vec.subst_size1 {t : T} :
--   (v[t] i)[σ] = (t[σ]::mk0) i
-- := by sorry

-- @[simp]
-- theorem Vec.subst_size2 {t1 t2 : T} :
--   (v[t1, t2] i)[σ] = (t1[σ]::t2[σ]::mk0) i
-- := by sorry

end OneSortHomArityGen
