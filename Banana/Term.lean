import LeanSubst
open LeanSubst

namespace Banana



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

#leansubst var Ty.var
#leansubst bind Ty at pos 1 in Ty.all
#leansubst generate Ty


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

#leansubst var Term.var
#leansubst bind Term at pos 1 in Term.lam
#leansubst bind Ty at pos 1 in Term.tlam

#leansubst generate Term, Ty

prefix:max "#" => Term.var
notation "λ[" A "]" t => Term.lam A t
notation "Λ[" K "]" B => Term.tlam K B
infixl:54 " • " => Term.app
notation f " •[" a "]" => Term.tapp f a

----------------------------------------------------------------------------------------------------
-- Substitution of Ty
----------------------------------------------------------------------------------------------------

-- @[coe]
-- def Ty.from_action : Action Ty -> Ty
-- | .re y => t#y
-- | .su t => t

-- @[simp]
-- theorem Ty.from_action_id {n} : from_action ((Subst.id Ty).act n) = t#n := by
--   simp [from_action, Subst.id]

-- @[simp]
-- theorem Ty.from_action_succ {n} : from_action ((Subst.add Ty 1).act n) = t#(n + 1) := by
--   simp [from_action, Subst.add]

-- @[simp]
-- theorem Ty.from_acton_re {n} : from_action (re n) = t#n := by simp [from_action]

-- -- @[simp]
-- -- theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

-- -- instance : Coe (Action Ty) Ty where
-- --   coe := Ty.from_action

-- -- @[simp]
-- -- def Ty.rmap (r : RenVec [Ty]) : Ty -> Ty
-- -- | t#x => t#(r.head.act x)
-- -- | A -:> B => rmap r A -:> rmap r B
-- -- | ∀[K] P => ∀[K] rmap (r.lift [1]) P
-- -- -- | λ[K] t => λ[K] rmap r.lift t
-- -- -- | app f a => rmap r f • rmap r a

-- instance : RenMap Ty [Ty] where
--   rmap := Ty.rmap

-- @[simp]
-- theorem Ty.ren_var {r : RenVec [Ty]}: (t#x)⟨r,⟩ = t#(r.head.act x) := by simp [RenMap.rmap]

-- @[simp]
-- theorem Ty.ren_arr {r : RenVec [Ty]} {A B : Ty} :(A -:> B)⟨r,⟩ = A⟨r,⟩ -:> B⟨r,⟩  := by simp [RenMap.rmap]

-- @[simp]
-- theorem Ty.ren_all {r : RenVec [Ty]}: (∀[K] P)⟨r,⟩ = ∀[K] P⟨r.lift [1],⟩ := by simp [RenMap.rmap]

-- -- @[simp]
-- -- theorem Ty.ren_lam {P : Ty} : (λ[K] P)⟨r⟩ = λ[K] P⟨r.lift⟩ := by simp [RenMap.rmap]

-- -- @[simp]
-- -- theorem Ty.ren_app {f a : Ty} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by simp [RenMap.rmap]

-- instance : RenMapId Ty [Ty] where
--   id_law := by sorry --subst_solve_id

-- instance : RenMapComp Ty [Ty] where
--   compose_law := by sorry --subst_solve_compose

-- instance : RenMapAll [Ty] := .cons .nil

-- @[simp]
-- def Ty.smap (σ : SubstVec [Ty]) : Ty -> Ty
-- | t#x => σ.head.act x
-- | A -:> B => smap σ A -:> smap σ B
-- | ∀[K] P => ∀[K] smap (σ.lift [1]) P
-- -- | λ[K] t => λ[K] smap σ.lift t
-- --| app f a => smap σ f • smap σ a

-- instance : SubstMap Ty [Ty] where
--   smap := Ty.smap

-- @[simp]
-- theorem Ty.subst_var {σ : SubstVec [Ty]} : (t#x)[σ,] = σ.head.act x := by simp [SubstMap.smap]

-- @[simp]
-- theorem Ty.subst_arr {σ : SubstVec [Ty]} {A B : Ty} : (A -:> B)[σ,] = A[σ,] -:> B[σ,] := by simp [SubstMap.smap]

-- instance : SubstMapAll [Ty] := .cons .nil

-- @[simp]
-- theorem Ty.subst_all {σ : SubstVec [Ty]} : (∀[K] P)[σ,] = ∀[K] P[σ.lift [1],] := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Ty.subst_lam {P : Ty} : (λ[K] P)[σ:Ty] = λ[K] P[σ.lift:_] := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Ty.subst_app {f a : Ty} : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Ty.from_action_compose {x} {σ : Subst Ty} {τ : SubstVec [Ty]}
--   : (from_action (σ.act x))[τ,] = from_action ((σ >> τ).act x)
-- := by
--   simp [Ty.from_action, Subst.compose]
--   generalize zdef : σ.act x = z
--   cases z <;> simp [Ty.from_action]

-- instance : SubstMapId Ty [Ty] where
--   id_law := by subst_solve_id

-- instance : SubstMapStable Ty [Ty] where
--   stable := by sorry --subst_solve_stable

-- instance : SubstMapRenCompLeft Ty [Ty] where
--   compose_left_law := by sorry --subst_solve_compose

-- instance : SubstMapRenCompRight Ty [Ty] where
--   compose_right_law := by sorry --subst_solve_compose

-- instance : SubstMapComp Ty [Ty] where
--   compose_law := by sorry --subst_solve_compose

-- ----------------------------------------------------------------------------------------------------
-- -- Substitution of Term
-- ----------------------------------------------------------------------------------------------------

-- @[coe]
-- def Term.from_action : Action Term -> Term
-- | .re y => #y
-- | .su t => t

-- @[simp]
-- theorem Term.from_action_id {n} : from_action ((Subst.id Term).act n) = #n := by
--   simp [from_action, Subst.id]

-- @[simp]
-- theorem Term.from_action_succ {n} : from_action ((Subst.add Term 1).act n) = #(n + 1) := by
--   simp [from_action, Subst.add]

-- @[simp]
-- theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

-- @[simp]
-- theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

-- instance : Coe (Action Term) Term where
--   coe := Term.from_action

-- -- @[simp]
-- -- def Term.Ty.rmap (r : HetRen Ty) : Term -> Term
-- -- | #x => #x
-- -- | λ[A] t => λ[A⟨r.forget⟩] rmap r t
-- -- | Λ[K] t => Λ[K] rmap r.lift t
-- -- | app f a => rmap r f • rmap r a
-- -- | f •[a] => rmap r f •[a⟨r.forget⟩]

-- -- instance : HetRenMap Term Ty where
-- --   hrmap := Term.Ty.rmap

-- -- @[simp]
-- -- theorem Term.Ty.ren_var {r : HetRen Ty} : (#x)⟨r⟩ = #x := by simp [HetRenMap.hrmap]

-- -- @[simp]
-- -- theorem Term.Ty.ren_lam {r : HetRen Ty} {t : Term} : (λ[A] t)⟨r⟩ = λ[A⟨r.forget⟩] t⟨r⟩ := by simp [HetRenMap.hrmap]

-- -- @[simp]
-- -- theorem Term.Ty.ren_tlam {r : HetRen Ty} {t : Term} : (Λ[K] t)⟨r⟩ = Λ[K] t⟨r.lift⟩ := by simp [HetRenMap.hrmap]

-- -- @[simp]
-- -- theorem Term.Ty.ren_app {r : HetRen Ty} {f a : Term} : (f • a)⟨r⟩ = f⟨r⟩ • a⟨r⟩ := by simp [HetRenMap.hrmap]

-- -- @[simp]
-- -- theorem Term.Ty.ren_tapp {r : HetRen Ty} {f : Term} : (f •[a])⟨r⟩ = f⟨r⟩ •[a⟨r.forget⟩] := by simp [HetRenMap.hrmap]

-- -- instance : HetRenMapId Term Ty where
-- --   apply_id := by subst_solve_id

-- -- instance : HetRenMapComp Term Ty where
-- --   apply_compose := by subst_solve_compose

-- @[simp]
-- def Term.rmap (r : RenVec [Term, Ty]) : Term -> Term
-- | #x => #(r.head.act x)
-- | λ[A] t => λ[A⟨r.tail,⟩] rmap (r.lift [1,0]) t
-- | Λ[K] t => Λ[K] rmap (r.lift [0,1]) t
-- | app f a => rmap r f • rmap r a
-- | f •[a] => rmap r f •[a⟨r.tail,⟩]

-- instance : RenMap Term [Term,Ty] where
--   rmap := Term.rmap

-- @[simp]
-- theorem Term.ren_var {r : RenVec [Term, Ty]} : (#x)⟨r,⟩ = #(r.head.act x) := by simp [RenMap.rmap]

-- @[simp]
-- theorem Term.ren_lam {t : Term} {r : RenVec [Term, Ty]}: (λ[A] t)⟨r,⟩ = λ[A⟨r.tail,⟩] t⟨r.lift [1,0],⟩ := by simp [RenMap.rmap]


-- @[simp]
-- theorem Term.ren_tlam {t : Term}  {r : RenVec [Term, Ty]}: (Λ[K] t)⟨r,⟩ = Λ[K] t⟨r.lift [0,1],⟩ := by simp [RenMap.rmap]

-- @[simp]
-- theorem Term.ren_app {f a : Term} {r : RenVec [Term, Ty]}: (f • a)⟨r,⟩ = f⟨r,⟩ • a⟨r,⟩ := by simp [RenMap.rmap]

-- @[simp]
-- theorem Term.ren_tapp {f : Term} {r : RenVec [Term, Ty]}: (f •[a])⟨r,⟩ = f⟨r,⟩ •[a⟨r.tail,⟩] := by simp [RenMap.rmap]

-- instance : RenMapId Term [Term, Ty] where
--   id_law := by sorry --subst_solve_id

-- instance : RenMapComp Term [Term, Ty] where
--   compose_law := by sorry --subst_solve_compose

-- instance : RenMapAll [Term, Ty] := .cons (.cons .nil)

-- @[simp]
-- def Term.smap (σ : SubstVec [Term, Ty]) : Term -> Term
-- | #x => σ.head.act x
-- | λ[A] t => λ[A[σ.tail,]] smap (σ.lift [1,0]) t
-- | Λ[K] t => Λ[K] smap (σ.lift [0,1]) t
-- | app f a => smap σ f • smap σ a
-- | f •[a] => smap σ f •[a[σ.tail,]]

-- instance : SubstMap Term [Term, Ty] where
--   smap := Term.smap

-- -- @[simp]
-- -- def Term.smap (σ : Subst Term) : Term -> Term
-- -- | #x => σ.act x
-- -- | λ[A] t => λ[A] smap σ.lift t
-- -- | Λ[K] t => Λ[K] smap (σ ◾ +1@Ty) t
-- -- | app f a => smap σ f • smap σ a
-- -- | f •[a] => smap σ f •[a]

-- instance : SubstMap Term [Term, Ty] where
--   smap := Term.smap

-- -- @[simp]
-- -- theorem Term.Ty.subst_var : (#x)[σ:Ty] = #x := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Term.Ty.subst_lam {t : Term} : (λ[A] t)[σ:Ty] = λ[A[σ:_]] t[σ:_] := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Term.Ty.subst_tlam : (Λ[K] t)[σ:Ty] = Λ[K] t[σ.lift:_] := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Term.Ty.subst_app {f a : Term} : (f • a)[σ:Ty] = f[σ:_] • a[σ:_] := by simp [SubstMap.smap]

-- -- @[simp]
-- -- theorem Term.Ty.subst_tapp : (f •[a])[σ:Ty] = f[σ:_] •[a[σ:_]] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_var {σ : SubstVec [Term, Ty]}: (#x)[σ,] = (σ.head.act x) := by simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_lam {σ : SubstVec [Term, Ty]} {t : Term} : (λ[A] t)[σ,] = λ[A[σ.tail,]] t[σ.lift [1,0],] :=
-- by
--   simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_tlam {σ : SubstVec [Term, Ty]} : (Λ[K] t)[σ,] = Λ[K] t[σ.lift [0,1],] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_app {f a : Term} {σ : SubstVec [Term, Ty]}: (f • a)[σ,] = f[σ,] • a[σ,] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Term.subst_tapp {σ : SubstVec [Term, Ty]}: (f •[a])[σ,] = f[σ,] •[a[σ.tail,]] := by simp [SubstMap.smap]

-- @[simp]
-- theorem Term.from_action_compose {x} {σ : Subst Term} {τ : SubstVec [Term, Ty]}
--   : (from_action (σ.act x))[τ,] = from_action ((σ >> τ).act x)
-- := by
--   simp [Term.from_action]
--   generalize zdef : σ.act x = z
--   cases z <;> simp [Term.from_action]

-- -- @[simp]
-- -- theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
-- --   : (σ ◾ τ).act x = (Term.from_action (σ.act x))[τ:Ty]
-- -- := by
-- --   simp [Subst.hcompose, Term.from_action]
-- --   generalize zdef : σ.act x = z
-- --   cases z <;> simp

-- instance : SubstMapId Term [Term, Ty] where
--   id_law := by subst_solve_id

-- instance : SubstMapStable Term [Term, Ty] where
--   stable := by sorry --subst_solve_stable

-- -- theorem Term.apply_ren_commute {s : Term} (r : Ren Ty) (τ : Subst Ty)
-- --   : s⟨r⟩[τ:Ty] = s[τ:Ty]⟨r⟩
-- -- := by
-- --   induction s generalizing r τ <;> simp at *
-- --   all_goals try simp [*]

-- -- instance : SubstMapRenCommute Term [Term, Ty] where
-- --   apply_ren_commute := Term.apply_ren_commute

-- instance : SubstMapRenCompLeft Term [Term, Ty] where
--   compose_left_law := by sorry --subst_solve_compose

-- instance : SubstMapRenCompRight Term [Term, Ty] where
--   compose_right_law := by sorry --subst_solve_compose

-- instance : SubstMapAll [Term, Ty] := .cons (.cons .nil)


-- instance : SubstMapComp Term [Term, Ty] where
--   compose_law := by sorry --subst_solve_compose

-- instance : SubstMapId Term [Term, Ty] where
--   id_law := by subst_solve_id

-- -- instance : SubstMapHetComp Term Ty where
-- --   apply_hcompose := by subst_solve_compose

-- instance : SubstMapRenCompLeft Term [Term, Ty] where
--   compose_left_law := by sorry --subst_solve_compose

-- instance : SubstMapRenCompRight Term [Term, Ty] where
--   compose_right_law := by sorry --subst_solve_compose

-- -- instance : SubstMapComp Term Term where
-- --   apply_compose := by subst_solve_compose

-- theorem Term.smap_promote : Term.smap σ t = t[σ,] := rfl

-- --theorem Term.Ty.smap_promote : Term.Ty.smap σ t = t[σ:Ty] := rfl

-- theorem Ty.smap_promote : Ty.smap σ T = T[σ,] := rfl

end Banana
