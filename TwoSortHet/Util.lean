import LeanSubst
open LeanSubst

def LeanSubst.HetRen.forget (r : HetRen T) : Ren  := ⟨r.act⟩

@[simp, grind =]
theorem LeanSubst.HetRen.forget_action {r : HetRen T} : r.forget.act = r.act := by simp [forget]

@[simp, grind =]
theorem LeanSubst.HetRen.forget_id : (HetRen.id T).forget = Ren.id := by
  simp [forget, id, Ren.id]

@[simp, grind =]
theorem LeanSubst.HetRen.forget_cons {r : HetRen T} : (n::r).forget = n::r.forget := by
  simp [forget, cons, Ren.cons]; congr

@[simp, grind =]
theorem LeanSubst.HetRen.forget_compose {r1 r2 : HetRen T} : (r1 ∘ r2).forget = r1.forget ∘ r2.forget := by
  simp [forget, compose, Ren.compose]

@[simp, grind =]
theorem LeanSubst.HetRen.forget_het {r : Ren} : (r.het T).forget = r := by
  simp [Ren.het, forget]

@[simp, grind =]
theorem LeanSubst.HetRen.het_forget {r : HetRen T} : r.forget.het T = r := by
  simp [Ren.het, forget]

@[simp, grind =]
theorem LeanSubst.Option.rmap_none [RenMap T] : (@none T)⟨r⟩ = none := by
  simp [RenMap.rmap, rmap]

@[simp, grind =]
theorem LeanSubst.Option.rmap_some [RenMap T] {t : T} : (some t)⟨r⟩ = some t⟨r⟩ := by
  simp [RenMap.rmap, rmap]

theorem LeanSubst.List.rmap_to_map [RenMap T] {ℓ : List T} : ℓ⟨r⟩ = ℓ.map (·⟨r⟩) := by
  induction ℓ <;> simp [RenMap.rmap, rmap]
  case _ ih => simp [RenMap.rmap] at ih; apply ih

@[simp, grind =]
theorem LeanSubst.List.rmap_index [RenMap T] {ℓ : List T} {x : Nat} : ℓ[x]?⟨r⟩ = ℓ⟨r⟩[x]? := by
  induction ℓ generalizing x <;> simp [RenMap.rmap, rmap, Option.rmap]
  case _ hd tl ih =>
  cases x <;> simp at *; case _ x =>
  simp [RenMap.rmap, Option.rmap] at ih
  apply ih
