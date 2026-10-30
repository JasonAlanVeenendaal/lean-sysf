
import Banana.Typing
import Banana.Kinding.Rename
import Banana.Kinding.Substitute
open LeanSubst

namespace Banana

structure TypingRen (r : Ren Term) (Γ1 Γ2 : List Ty) where
  act : ∀ {x T}, Γ1[x]? = some T -> Γ2[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ1 Γ2 : List Ty} A : Γ1 -⟨r⟩> Γ2 -> A::Γ1 -⟨r.lift⟩> A::Γ2
| j => .mk @λ x T h =>
  match x with
  | 0 => by simp at *; subst h; rfl
  | n + 1 =>
    have lem := j.act h
    by simp [Ren.lift] at *; apply lem

-- theorem TypingRen.rename {Γ1 : List Ty} k : {Γ2 : List Ty} -> Γ1 -⟨r⟩> Γ2 -> Γ1⟨k⟩ -⟨r⟩> Γ2⟨k⟩
-- | .nil, ⟨a⟩ => mk λ {x T} h => by
--   simp at *
--   rw [List.rmap_to_map] at h; simp at h
--   rcases h with ⟨q, h1, h2⟩
--   subst h2; apply a h1
-- | .cons hd Γ2, m => mk λ {x T} h => by
--   simp
--   rw [List.rmap_to_map] at h; simp at h
--   rcases h with ⟨q, h1, h2⟩; subst h2
--   have lem := m.act h1
--   generalize zdef : r.act x = z at *
--   cases z <;> simp at *; subst lem; rfl
--   case _ z =>
--     have lem2 : Γ2⟨k⟩[z]? = (some q)⟨k⟩ := by rw [<-lem]; simp
--     simp at lem2; exact lem2

theorem TypingRen.id (X : List Ty) : X -⟨.id Term⟩> X := .mk λ h => h

theorem TypingRen.succ {X : List Ty} : X -⟨Ren.add Term 1⟩> A::X := .mk λ h => h

theorem TypingRen.comp {A B C : List Ty} : A -⟨r1⟩> B -> B -⟨r2⟩> C -> A -⟨r1 >> r2⟩> C
| h1, h2 => .mk λ h =>
  have lem1 := h1.act h
  have lem2 := h2.act lem1
  lem2

-- def Typing.rename_type {Δ1 Δ2 : List Kind} (m : Δ1 -⟨r1⟩> Δ2)
--   : Δ1&Γ ⊢ t : A -> Δ2&Γ⟨r⟩ ⊢ t⟨r⟩ : A⟨r1⟩
-- | var (x := x) h j =>
--   let h' : Γ⟨r⟩[x]? = (some A)⟨r⟩ := by rw [<-h]; simp
--   var h' (j.rename m)
-- | lam j1 j2 => lam (j1.rename m) (j2.rename_type m)
-- | app j1 j2 => app (j1.rename_type m) (j2.rename_type m)
-- | tlam j =>
--   let j' := j.rename_type $ m.lift _
--   tlam $ j' |> cast (by sorry)
-- | tapp (P := P) (a := a) j1 j2 e =>
--   let e' : A⟨r⟩ = P⟨r.lift⟩[su a⟨r⟩ .: (Ren.add Ty 1)] := by
--     simp [e]
--     rw [Subst.apply_stable r.lift r.to.lift Ren.to_lift]
--     rw [Subst.apply_stable r _ rfl]
--     simp
--   tapp (P := P⟨r.lift⟩) (j1.rename_type m) (j2.rename m) e'
-- --| conv j1 cv j2 => sorry

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem : Γ⟨.add Ty k⟩[x]?⟨.sub Ty k⟩ = some T⟨.sub Ty k⟩ := by simp [h]
  by {
    simp at lem; replace act := act lem
    rw [<-List.rmap_getElem?, act]
    rw [<-Option.rmap_some, <-h]
    simp
  }⟩

-- def Typing.rename {Δ1 Δ2 : List Kind} {Γ1 Γ2 : List Ty}
--   (m1 : Δ1 -⟨r1⟩> Δ2) (m2 : Γ1 -⟨r2⟩> Γ2)
--   : Δ1&Γ1 ⊢ t : A -> Δ2&Γ2⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
-- | var (x := x) j1 j2 =>
--   have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
--   var (simp% j1) (j2.rename m1)
-- | app j1 j2 => app (j1.rename m1 m2) (j2.rename m1 m2)
-- | lam (A := A) j1 j2 => lam (j1.rename m1) (j2.rename m1 $ m2.lift A)
-- | tapp j1 j2 e => tapp (j1.rename m1 m2) (j2.rename m1) (by simp [e])
-- | tlam (K := K) j =>
--   have lem1 := m1.lift K
--   have lem2 := m2.shift 1
--   have lem3 := j.rename lem1 lem2
--   tlam (by simp; sorry)--lsimp j.rename (m1.lift K) (m2.shift 1))
-- | var h j => var (m.act h) j
-- | lam j1 j2 => lam j1 $ j2.rename (m.lift _)
-- | app j1 j2 => app (j1.rename m) (j2.rename m)
-- | tlam j => tlam $ j.rename $ m.rename (Ren.add 1)
-- | tapp j1 j2 e => tapp (j1.rename m) j2 e
--| conv j1 cv j2 => sorry

end Banana
