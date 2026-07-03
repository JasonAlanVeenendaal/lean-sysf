
import TwoSortHet.Util
import LeanSubst
open LeanSubst

namespace TwoSortHet

----------------------------------------------------------------------------------------------------
-- Syntax
----------------------------------------------------------------------------------------------------

inductive Kind where
| base : Kind

notation "★" => Kind.base
--infixr:64 " -:> " => Kind.arrow

inductive Ty where
| var : Nat -> Ty
--| app : Ty -> Ty -> Ty
--| lam : Kind -> Ty -> Ty
| all : Kind -> Ty -> Ty
| arrow : Ty -> Ty -> Ty

prefix:max "t#" => Ty.var
infixr:64 " -:> " => Ty.arrow
--notation "λ[" K "]" t => Ty.lam K t
notation "∀[" K "]" B => Ty.all K B
--infixl:54 " • " => Ty.app

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term
| tapp : Term -> Ty -> Term
| tlam : Kind -> Term -> Term

prefix:max "#" => Term.var
notation "λ[" A "]" t => Term.lam A t
notation "Λ[" K "]" B => Term.tlam K B
infixl:54 " • " => Term.app
notation f " •[" a "]" => Term.tapp f a

----------------------------------------------------------------------------------------------------
-- Substitution of Ty
----------------------------------------------------------------------------------------------------

@[coe]
def Ty.from_action : Subst.Action Ty -> Ty
| .re y => t#y
| .su t => t

@[simp]
theorem Ty.from_action_id {n} : from_action (+0.act n) = t#n := by
  simp [from_action, Subst.id]

@[simp]
theorem Ty.from_action_succ {n} : from_action (+1.act n) = t#(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Ty.from_acton_re {n} : from_action (re n) = t#n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (r : Ren) : Ty -> Ty
| t#x => t#(r.act x)
| A -:> B => rmap r A -:> rmap r B
| ∀[K] P => ∀[K] rmap r.lift P
-- | λ[K] t => λ[K] rmap r.lift t
-- | app f a => rmap r f • rmap r a

instance : RenMap Ty where
  rmap := Ty.rmap

@[simp]
theorem Ty.ren_var : (t#x)⟨r⟩ = t#(r.act x) := by simp [RenMap.rmap]

@[simp]
theorem Ty.ren_arr {A B : Ty} : (A -:> B)⟨r⟩ = A⟨r⟩ -:> B⟨r⟩ := by simp [RenMap.rmap]

@[simp]
theorem Ty.ren_all : (∀[K] P)⟨r⟩ = ∀[K] P⟨r.lift⟩ := by simp [RenMap.rmap]

-- @[simp]
-- theorem Ty.ren_lam {P : Ty} : (λ[K] P)⟨r⟩ = λ[K] P⟨r.lift⟩ := by simp [RenMap.rmap]

-- @[simp]
-- theorem Ty.ren_app {f a : Ty} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by simp [RenMap.rmap]

instance : RenMapId Ty where
  apply_id := by subst_solve_id

instance : RenMapCompose Ty where
  apply_compose := by subst_solve_compose

@[simp]
def Ty.smap (σ : Subst Ty) : Ty -> Ty
| t#x => σ.act x
| A -:> B => smap σ A -:> smap σ B
| ∀[K] P => ∀[K] smap σ.lift P
-- | λ[K] t => λ[K] smap σ.lift t
--| app f a => smap σ f • smap σ a

instance : SubstMap Ty Ty where
  smap := Ty.smap

@[simp]
theorem Ty.subst_var : (t#x)[σ:Ty] = σ.act x := by simp [SubstMap.smap]

@[simp]
theorem Ty.subst_arr {A B : Ty} : (A -:> B)[σ:Ty] = A[σ:_] -:> B[σ:_] := by simp [SubstMap.smap]

@[simp]
theorem Ty.subst_all : (∀[K] P)[σ:Ty] = ∀[K] P[σ.lift:_] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Ty.subst_lam {P : Ty} : (λ[K] P)[σ:Ty] = λ[K] P[σ.lift:_] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Ty.subst_app {f a : Ty} : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_compose {x} {σ τ : Subst Ty}
  : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
:= by
  simp [Ty.from_action, Subst.compose]
  generalize zdef : σ.act x = z
  cases z <;> simp [Ty.from_action]

instance : SubstMapId Ty Ty where
  apply_id := by subst_solve_id

instance : SubstMapStable Ty where
  apply_stable := by subst_solve_stable

instance : SubstMapRenComposeLeft Ty Ty where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Ty Ty where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Ty Ty where
  apply_compose := by subst_solve_compose

----------------------------------------------------------------------------------------------------
-- Substitution of Term
----------------------------------------------------------------------------------------------------

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0.act n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1.act n) = #(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.Ty.rmap (r : HetRen Ty) : Term -> Term
| #x => #x
| λ[A] t => λ[A⟨r.forget⟩] rmap r t
| Λ[K] t => Λ[K] rmap r.lift t
| app f a => rmap r f • rmap r a
| f •[a] => rmap r f •[a⟨r.forget⟩]

instance : HetRenMap Term Ty where
  hrmap := Term.Ty.rmap

@[simp]
theorem Term.Ty.ren_var {r : HetRen Ty} : (#x)⟨r⟩ = #x := by simp [HetRenMap.hrmap]

@[simp]
theorem Term.Ty.ren_lam {r : HetRen Ty} {t : Term} : (λ[A] t)⟨r⟩ = λ[A⟨r.forget⟩] t⟨r⟩ := by simp [HetRenMap.hrmap]

@[simp]
theorem Term.Ty.ren_tlam {r : HetRen Ty} {t : Term} : (Λ[K] t)⟨r⟩ = Λ[K] t⟨r.lift⟩ := by simp [HetRenMap.hrmap]

@[simp]
theorem Term.Ty.ren_app {r : HetRen Ty} {f a : Term} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by simp [HetRenMap.hrmap]

@[simp]
theorem Term.Ty.ren_tapp {r : HetRen Ty} {f : Term} : (f •[a])⟨r⟩ = f⟨r⟩ •[a⟨r.forget⟩] := by simp [HetRenMap.hrmap]

instance : HetRenMapId Term Ty where
  apply_id := by subst_solve_id

instance : HetRenMapCompose Term Ty where
  apply_compose := by subst_solve_compose

@[simp]
def Term.rmap (r : Ren) : Term -> Term
| #x => #(r.act x)
| λ[A] t => λ[A] rmap r.lift t
| Λ[K] t => Λ[K] rmap r t
| app f a => rmap r f • rmap r a
| f •[a] => rmap r f •[a]

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
theorem Term.ren_var : (#x)⟨r⟩ = #(r.act x) := by simp [RenMap.rmap]

@[simp]
theorem Term.ren_lam {t : Term} : (λ[A] t)⟨r⟩ = λ[A] t⟨r.lift⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.ren_tlam {t : Term} : (Λ[K] t)⟨r⟩ = Λ[K] t⟨r⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.ren_app {f a : Term} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.ren_tapp {f : Term} : (f •[a])⟨r⟩ = f⟨r⟩ •[a] := by simp [RenMap.rmap]

instance : RenMapId Term where
  apply_id := by subst_solve_id

instance : RenMapCompose Term where
  apply_compose := by subst_solve_compose

@[simp]
def Term.Ty.smap (σ : Subst Ty) : Term -> Term
| #x => #x
| λ[A] t => λ[A[σ:_]] smap σ t
| Λ[K] t => Λ[K] smap σ.lift t
| app f a => smap σ f • smap σ a
| f •[a] => smap σ f •[a[σ:_]]

instance : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| #x => σ.act x
| λ[A] t => λ[A] smap σ.lift t
| Λ[K] t => Λ[K] smap (σ ◾ +1@Ty) t
| app f a => smap σ f • smap σ a
| f •[a] => smap σ f •[a]

instance : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.Ty.subst_var : (#x)[σ:Ty] = #x := by simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam {t : Term} : (λ[A] t)[σ:Ty] = λ[A[σ:_]] t[σ:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tlam : (Λ[K] t)[σ:Ty] = Λ[K] t[σ.lift:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_app {f a : Term} : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tapp : (f •[a])[σ:Ty] = f[σ:_] •[a[σ:_]] := by simp [SubstMap.smap]

@[simp]
theorem Term.subst_var : (#x)[σ:Term] = σ.act x := by simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam {t : Term} : (λ[A] t)[σ:Term] = λ[A] t[σ.lift:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.subst_tlam : (Λ[K] t)[σ:Term] = Λ[K] t[σ ◾ +1@Ty:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.subst_app {f a : Term} : (f • a)[σ:Term] = f[σ:_] • a[σ:_] := by simp [SubstMap.smap]

@[simp]
theorem Term.subst_tapp : (f •[a])[σ:Term] = f[σ:_] •[a] := by simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ.act x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ).act x = (Term.from_action (σ.act x))[τ:Ty]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

instance : SubstMapId Term Ty where
  apply_id := by subst_solve_id

instance : SubstMapStable Term where
  apply_stable := by subst_solve_stable

theorem Term.apply_ren_commute {s : Term} (r : Ren) (τ : Subst Ty)
  : s⟨r⟩[τ:Ty] = s[τ:Ty]⟨r⟩
:= by
  induction s generalizing r τ <;> simp at *
  all_goals try simp [*]

instance : SubstMapRenCommute Term Ty where
  apply_ren_commute := Term.apply_ren_commute

instance : SubstMapRenComposeLeft Term Ty where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term Ty where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Term Ty where
  apply_compose := by subst_solve_compose

instance : SubstMapId Term Term where
  apply_id := by subst_solve_id

instance : SubstMapHetCompose Term Ty where
  apply_hcompose := by subst_solve_compose

instance : SubstMapRenComposeLeft Term Term where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term Term where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Term Term where
  apply_compose := by subst_solve_compose

end TwoSortHet
