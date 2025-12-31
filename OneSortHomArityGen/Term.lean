
import OneSortHomArityGen.Vec
import LeanSubst

open LeanSubst

inductive VariantSort where
| bind | ctor

inductive Variant : VariantSort -> Nat -> Type where
| star : Variant .ctor 0
| app : Variant .ctor 2
| tapp : Variant .ctor 2
| arr : Variant .ctor 2
| lam : Variant .bind 1
| tlam : Variant .bind 0
| all : Variant .bind 0

inductive Term where
| var : Nat -> Term
| bind {n} : (v : Variant .bind n) -> Vec Term n -> Term -> Term
| ctor {n} : (v : Variant .ctor n) -> Vec Term n -> Term

protected def Term.repr (t : Term) (p : Nat) : Std.Format :=
  match t with
  | var x => "#" ++ Nat.repr x
  | ctor .star _ => "★"
  | ctor .arr ts => Term.repr (ts 0) p ++ " -> " ++ Term.repr (ts 1) p
  | ctor .app ts => Term.repr (ts 0) p ++ " " ++ Term.repr (ts 1) p
  | ctor .tapp ts => Term.repr (ts 0) p  ++ "[" ++ Term.repr (ts 1) p ++ "]"
  | bind .all _ t => "∀ " ++ Term.repr t p
  | bind .lam ts t => "λ[" ++ Term.repr (ts 0) p ++ "] " ++ Term.repr t p
  | bind .tlam _ t => "Λ " ++ Term.repr t p

instance : Repr Term where
  reprPrec := Term.repr

notation "★" => Term.ctor Variant.star Vec.nil
prefix:max "#" => Term.var
notation:65 f:65 " :@ " a:64 => Term.ctor Variant.app (f::a::Vec.nil)
notation:65 f:65 " :@[" a "]" => Term.ctor Variant.tapp (f::a::Vec.nil)
notation ":λ[" A "] " t => Term.bind Variant.lam (A::Vec.nil) t
notation:64 A:63 " -:> " B:64 => Term.ctor Variant.arr (A::B::Vec.nil)
notation ":∀ " t => Term.bind Variant.all Vec.nil t
notation "Λ " t => Term.bind Variant.tlam Vec.nil t

@[app_unexpander Term.ctor]
meta def unexpand_term_ctor : Lean.PrettyPrinter.Unexpander
| `($(_) Variant.star v[]) => `(★)
| `($(_) Variant.app v[$f, $a]) => `($f :@ $a)
| `($(_) Variant.tapp v[$f, $a]) => `($f :@[$a])
| `($(_) Variant.arr v[$a, $b]) => `($a -:> $b)
| _ => throw ()

@[app_unexpander Term.bind]
meta def unexpand_term_bind : Lean.PrettyPrinter.Unexpander
| `($(_) Variant.lam v[$a] $t) => `(:λ[ $a ] $t)
| `($(_) Variant.tlam v[] $t) => `(Λ $t)
| `($(_) Variant.all v[] $t) => `(:∀ $t)
| _ => throw ()

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
def Term.rmap (lf : Endo Ren) (r : Ren) : Term -> Term
| var x => var (r x)
| ctor v ts => ctor v (λ i => rmap lf r (ts i))
| bind v ts t => bind v (λ i => rmap lf r (ts i)) (rmap lf (lf r) t)

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
def Term.smap (lf : Endo (Subst Term)) (σ : Subst Term) : Term -> Term
| var x => σ x
| ctor v ts => ctor v (λ i => smap lf σ (ts i))
| bind v ts t => bind v (λ i => smap lf σ (ts i)) (smap lf (lf σ) t)

instance SubstMap_Term : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem subst_var : (#x)[σ:Term] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_bind
  : (Term.bind v ts t)[σ:Term] = .bind v (λ i => (ts i)[σ:_]) t[σ.lift:_]
:= by unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_ctor : (Term.ctor v ts)[σ:Term] = .ctor v (λ i => (ts i)[σ:_]) := by
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

instance : SubstMapId Term Term where
  apply_id := apply_id

theorem apply_stable (r : Ren) (σ : Subst Term)
  : r.to = σ -> Ren.apply (T := Term) r = Subst.apply σ
:= by solve_stable Term, r, σ

instance : SubstMapStable Term Term where
  apply_stable := apply_stable

theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  solve_compose Term, s, σ, τ

instance SubstMapCompose_Term : SubstMapCompose Term Term where
  apply_compose := apply_compose

@[simp]
theorem ren_apply_to_var : Term.from_action (Ren.to r x) = Term.var (r x) := by
  simp [Ren.to]

theorem Term.ren_eq_star {r : Ren} : t[r] = ★ -> t = ★ := by
  intro h; induction t generalizing r <;> simp at *
  case _ v ts ih =>
  cases h; case _ h1 h2 =>
  subst h1; simp at *; apply h2
