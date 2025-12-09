
import LeanSubst

inductive Ctor2Kind where
| app | tapp | arr

inductive Bind1Kind where
| tlam | all

inductive Term where
| star : Term
| var : Nat -> Term
| lam : Term -> Term -> Term
| bind1 : Bind1Kind -> Term -> Term
| ctor2 : Ctor2Kind -> Term -> Term -> Term

inductive IsVar : Term -> Prop where
| var : IsVar (.var x)

def Var := { t : Term // IsVar t }

inductive IsLam : Term -> Prop where
| var : IsLam (.var x)
| lam : IsLam A -> IsLam t -> IsLam (.lam A t)

def Lam := {t : Term // IsLam t}

namespace Var
  def var (x : Nat) : Var := .mk (.var x) (by constructor)

  @[simp]
  def out : Var -> Nat
  | .mk (.var x) _ => x
end Var

@[simp]
instance instCoe_Var_Term : Coe Var Term where
  coe := λ v => v.val

protected def Term.repr (a : Term) (p : Nat) : Std.Format :=
  match a with
  | .star => "★"
  | .var x => "#" ++ Nat.repr x
  | .lam A t => "(λ[" ++ Term.repr A p ++ "] " ++ Term.repr t p ++ ")"
  | .bind1 .all P => "(∀" ++ Term.repr P p ++  ")"
  | .bind1 .tlam P => "(Λ" ++ Term.repr P p ++  ")"
  | .ctor2 .app f a => "(" ++ Term.repr f p ++ " " ++ Term.repr a p ++ ")"
  | .ctor2 .tapp f a => "(" ++ Term.repr f p ++ "·" ++ Term.repr a p ++ ")"
  | .ctor2 .arr A B => "(" ++ Term.repr A p ++ " -> " ++ Term.repr B p ++ ")"

instance : Repr Term where
  reprPrec := Term.repr

notation "★" => Term.star
prefix:max "#" => Term.var
notation:65 f:65 " :@ " a:64 => Term.ctor2 Ctor2Kind.app f a
notation:65 f:65 " :@[" a "]" => Term.ctor2 Ctor2Kind.tapp f a
notation ":λ[" A "] " t => Term.lam A t
notation:64 A:63 " -:> " B:64 => Term.ctor2 Ctor2Kind.arr A B
notation ":∀ " t => Term.bind1 Bind1Kind.all t
notation "Λ " t => Term.bind1 Bind1Kind.tlam t

namespace Term
  @[simp]
  def size : Term -> Nat
  | ★ => 0
  | .var _ => 0
  | .lam A t => size A + size t + 1
  | .bind1 _ t => size t + 1
  | .ctor2 _ t1 t2 => size t1 + size t2 + 1
end Term

open LeanSubst


@[simp]
def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
| ★ => ★
| .var x =>
  match f x with
  | .re y => .var y
  | .su t => t
| .lam A t => .lam (smap lf f A) (smap lf (lf f) t)
| .bind1 k t => .bind1 k (smap lf (lf f) t)
| .ctor2 k t1 t2 => .ctor2 k (smap lf f t1) (smap lf f t2)

instance SubstMap_Term : SubstMap Term where
  smap := smap

@[simp]
theorem smap_to_notation : smap Subst.lift σ t = t[σ] := by
  unfold Subst.apply
  unfold SubstMap.smap
  unfold SubstMap_Term
  simp

@[simp]
theorem subst_star : ★[σ] = ★ := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_var :
  (#x)[σ] = match σ x with | .re y => .var y | .su t => t
:= by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_lam : (:λ[A] t)[σ] = :λ[A[σ]] t[σ.lift] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_bind1 : (Term.bind1 k t)[σ] = .bind1 k (t[σ.lift]) := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_ctor2 : (Term.ctor2 k t1 t2)[σ] = .ctor2 k (t1[σ]) (t2[σ]) := by
  unfold Subst.apply; simp [SubstMap.smap]

theorem apply_id {t : Term} : t[I] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

theorem apply_stable {r : Ren} {σ : Subst Term}
  : r.to = σ -> Ren.apply r = Subst.apply σ
:= by solve_stable r, σ

instance SubstMapStable_Term : SubstMapStable Term where
  apply_id := apply_id
  apply_stable := apply_stable

theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  solve_compose Term, s, σ, τ

instance SubstMapCompose_Term : SubstMapCompose Term where
  apply_compose := apply_compose

namespace LeanSubst.Subst
  namespace Action
    @[simp, coe]
    def coe [Coe A B] : Subst.Action A -> Subst.Action B
    | .re x => .re x
    | .su t => .su t

    @[simp]
    def coe_re [Coe A B] : coe (A := A) (B := B) (#x) = PrefixHash.hash x := by
      unfold coe; simp

    @[simp]
    def coe_su [i : Coe A B] :
      @coe A B i (%t) = PrefixPercent.percent (T := B) (F := Subst.Action) t
    := by
      unfold coe; simp

    @[simp]
    def var : Subst.Action Var -> Nat
    | .re x => x
    | .su t => t.out
  end Action
end LeanSubst.Subst

instance instCoe_SubstAction_from_Coe [Coe A B] : Coe (Subst.Action A) (Subst.Action B) where
  coe := Subst.Action.coe

namespace Subst
  @[simp, coe]
  def coe [Coe A B] : Subst A -> Subst B
  | σ, n => σ n

  class CommutesWithSmap (A B) [SubstMap A] [SubstMap B] [c : Coe A B] where
    coe_commutes : ∀ a (σ : Subst A), Coe.coe (a[σ]) = (Coe.coe a)[@coe _ _ c σ]

  @[simp]
  theorem coe_cons {a : Subst.Action A} {σ : Subst A} [Coe A B]
    : coe (a :: σ) = ↑a :: (coe (B := B) σ)
  := by
    funext; case _ x =>
    simp; cases x <;> simp

  @[simp]
  theorem coe_comp {σ τ : Subst A}
    [SubstMap A] [SubstMap B] [Coe A B] [i : CommutesWithSmap A B]
    : coe (σ ∘ τ) = coe (B := B) σ ∘ coe τ
  := by
    funext; case _ x =>
    simp [Subst.compose]
    generalize zdef : σ x = z at *
    cases z <;> simp
    case _ a =>
      rw [CommutesWithSmap.coe_commutes]
end Subst

instance instCoe_Subst_from_Coe [Coe A B] : Coe (Subst A) (Subst B) where
  coe := Subst.coe
