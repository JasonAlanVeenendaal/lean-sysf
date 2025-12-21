
import LeanSubst

open LeanSubst

inductive VariantSort where
| bind | ctor

inductive Variant : VariantSort -> Type where
| star : Variant .ctor
| app : Variant .ctor
| tapp : Variant .ctor
| arr : Variant .ctor
| lam : Variant .bind
| tlam : Variant .bind
| all : Variant .bind

@[reducible]
def Variant.arity : Variant s -> Nat
| star | tlam | all => 0
| app | tapp | arr => 2
| lam => 1

inductive Term where
| var : Nat -> Term
| bind : (v : Variant .bind) -> (Fin v.arity -> Term) -> Term -> Term
| ctor : (v : Variant .ctor) -> (Fin v.arity -> Term) -> Term

-- protected def Term.repr (a : Term) (p : Nat) : Std.Format :=
--   match a with
--   | .star => "★"
--   | .var x => "#" ++ Nat.repr x
--   | .lam A t => "(λ[" ++ Term.repr A p ++ "] " ++ Term.repr t p ++ ")"
--   | .bind1 .all P => "(∀" ++ Term.repr P p ++  ")"
--   | .bind1 .tlam P => "(Λ" ++ Term.repr P p ++  ")"
--   | .ctor2 .app f a => "(" ++ Term.repr f p ++ " " ++ Term.repr a p ++ ")"
--   | .ctor2 .tapp f a => "(" ++ Term.repr f p ++ "·" ++ Term.repr a p ++ ")"
--   | .ctor2 .arr A B => "(" ++ Term.repr A p ++ " -> " ++ Term.repr B p ++ ")"

-- instance : Repr Term where
--   reprPrec := Term.repr

notation "★" => Term.ctor Variant.star mk0
prefix:max "#" => Term.var
notation:65 f:65 " :@ " a:64 => Term.ctor Variant.app (λ i => mk2 f a i)
notation:65 f:65 " :@[" a "]" => Term.ctor Variant.tapp (λ i => mk2 f a i)
notation ":λ[" A "] " t => Term.bind Variant.lam (λ i => mk1 A i) t
notation:64 A:63 " -:> " B:64 => Term.ctor Variant.arr (λ i => mk2 A B i)
notation ":∀ " t => Term.bind Variant.all mk0 t
notation "Λ " t => Term.bind Variant.tlam mk0 t

@[simp]
instance : Inhabited Term where
  default := ★

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0 n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1 n) = #(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance instCoe_SubstActionTerm_Term : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def smap (k : Subst.Kind) (lf : Subst.Lift Term k) (f : SplitSubst Term k) : Term -> Term
| .var x =>
  match k with
  | .re => #(f x)
  | .su => f x
| .ctor v ts => .ctor v (λ i => smap k lf f (ts i))
| .bind v ts t => .bind v (λ i => smap k lf f (ts i)) (smap k lf (lf f) t)

instance SubstMap_Term : SubstMap Term where
  smap := smap

theorem smap_to_notation : smap .su Subst.lift σ t = t[σ] := by
  unfold Subst.apply
  unfold SubstMap.smap
  unfold SubstMap_Term
  simp

@[simp]
theorem subst_var : (#x)[σ] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_bind
  : (Term.bind v ts t)[σ] = .bind v (λ i => (ts i)[σ]) t[σ.lift]
:= by unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_ctor : (Term.ctor v ts)[σ] = .ctor v (λ i => (ts i)[σ]) := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

theorem apply_id {t : Term} : t[+0] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

theorem apply_stable (r : Ren) (σ : Subst Term)
  : r.to = σ -> Ren.apply r = Subst.apply σ
:= by solve_stable r, σ

instance SubstMapStable_Term : SubstMapStable Term where
  apply_id := apply_id
  apply_stable := apply_stable

theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  solve_compose Term, s, σ, τ

instance SubstMapCompose_Term : SubstMapCompose Term where
  apply_compose := apply_compose

@[simp]
theorem ren_apply_to_var : Term.from_action (Ren.to r x) = Term.var (r x) := by
  simp [Ren.to]

theorem Term.ren_eq_star {r : Ren} : t[r] = ★ -> t = ★ := by
  intro h; induction t generalizing r <;> simp at *
  case _ v ts ih =>
  cases h; case _ h1 h2 =>
  subst h1; simp at *
