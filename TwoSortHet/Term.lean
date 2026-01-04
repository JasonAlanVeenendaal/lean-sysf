
import LeanSubst
import TwoSortHet.Ty

namespace TwoSortHet

open LeanSubst

inductive Term : Type where
| var : Nat -> Term
| app : Term -> Term -> Term
| tapp : Term -> Ty -> Term
| lam : Ty -> Term -> Term
| tlam : Term -> Term

prefix:max "#" => Term.var
notation:65 f:65 " :@ " a:64 => Term.app f a
notation:65 f:65 " :@[" a "]" => Term.tapp f a
notation ":λ[" A "] " t => Term.lam A t
notation "Λ " t => Term.tlam t

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

instance : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (lf : Endo Ren) (r : Ren) : Term -> Term
| #x => #(r x)
| f :@ a => rmap lf r f :@ rmap lf r a
| f :@[a] => rmap lf r f :@[a]
| :λ[A] t => :λ[A] rmap lf (lf r) t
| Λ t => Λ rmap lf r t

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
def Term.Ty.smap (lf : Endo (Subst Ty)) (σ : Subst Ty) : Term -> Term
| #x => #x
| f :@ a => smap lf σ f :@ smap lf σ a
| f :@[a] => smap lf σ f :@[a[σ]]
| :λ[A] t => :λ[A[σ]] smap lf σ t
| Λ t => Λ smap lf (lf σ) t

instance : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (lf : Endo (Subst Term)) (σ : Subst Term) : Term -> Term
| #x => σ x
| f :@ a => smap lf σ f :@ smap lf σ a
| f :@[a] => smap lf σ f :@[a]
| :λ[A] t => :λ[A] smap lf (lf σ) t
| Λ t => Λ smap lf (σ ◾ +1@Ty) t

instance : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var : (#x)[σ:Term] = σ x := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_app : (f :@ a)[σ:Term] = f[σ:_] :@ a[σ:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_tapp : (f :@[a])[σ:Term] = f[σ:_] :@[a] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam : (:λ[A] t)[σ:Term] = :λ[A] t[σ.lift:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.subst_tlam : (Λ t)[σ:Term] = Λ t[σ ◾ +1@Ty:_] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.subst_var : (#x)[σ:Ty] = #x := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_app : (f :@ a)[σ:Ty] = f[σ:_] :@ a[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tapp : (f :@[a])[σ:Ty] = f[σ:_] :@[a[σ:Ty]] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam : (:λ[A] t)[σ:Ty] = :λ[A[σ:Ty]] t[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tlam : (Λ t)[σ:Ty] = Λ t[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap]

theorem Term.Ty.apply_id {t : Term} : t[+0:Ty] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

instance : SubstMapId Term Ty where
  apply_id := Term.Ty.apply_id

@[simp]
theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ) x = (Term.from_action (σ x))[τ:Ty]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ x = z
  cases z <;> simp

theorem Term.apply_stable (r : Ren) (σ : Subst Term)
  : r.to = σ -> Ren.apply (T := Term) r = Subst.apply σ
:= by subst_solve_stable Term, r, σ

instance : SubstMapStable Term where
  apply_stable := Term.apply_stable

theorem Term.apply_ren_commute {s : Term} (r : Ren) (τ : Subst Ty)
  : s[r.to][τ:Ty] = s[τ:Ty][r.to]
:= by
  induction s generalizing r τ <;> simp [Ren.to] at *
  all_goals try simp [*]
  case lam A t ih =>
    replace ih := ih r.lift
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    apply ih

instance : SubstMapRenCommute Term Ty where
  apply_ren_commute := Term.apply_ren_commute

theorem Term.Ty.apply_compose {s : Term} {σ τ : Subst Ty} : s[σ:Ty][τ:_] = s[σ ∘ τ:_] := by
  subst_solve_compose Ty, s, σ, τ

instance : SubstMapCompose Term Ty where
  apply_compose := Term.Ty.apply_compose

theorem Term.apply_hcompose {s : Term} {σ : Subst Term} {τ : Subst Ty}
  : s[σ][τ:_] = s[τ:_][σ ◾ τ]
:= by subst_solve_hcompose Term, Ty, s, σ, τ

instance : SubstMapHetCompose Term Ty where
  apply_hcompose := Term.apply_hcompose

theorem Term.apply_id {t : Term} : t[+0] = t := by subst_solve_id Term, Ty, t

instance : SubstMapId Term Term where
  apply_id := Term.apply_id

theorem Term.apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Term, s, σ, τ

instance : SubstMapCompose Term Term where
  apply_compose := Term.apply_compose

end TwoSortHet
