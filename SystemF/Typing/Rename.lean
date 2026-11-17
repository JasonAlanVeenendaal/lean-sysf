import SystemF.Typing
import SystemF.Kinding.Substitute
open LeanSubst

namespace SystemF

structure TypingRen (r : Ren Term) (Γ Γ' : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Γ'[r.act x]? = some T

theorem TypingRen.id Γ : TypingRen (.id Term) Γ Γ := ⟨λ j => j⟩

theorem TypingRen.add Γ A : TypingRen (.add Term A.length) Γ (A ++ Γ) :=
  ⟨λ j => by simp; rw [List.getElem?_append_right (by lia)]; simp [j]⟩

theorem TypingRen.lift {Γ Γ' r} (m : TypingRen r Γ Γ') (A : List Ty)
  : TypingRen (r.lift A.length) (A ++ Γ) (A ++ Γ')
:= ⟨λ {x} _ j =>
    match x.decLt A.length with
    | isTrue h =>
      simp% [-Ren.lift, Ren.lift_act_lt h, List.getElem?_append_left h] j
    | isFalse h => by
      replace h : x ≥ A.length := by lia
      rw [Ren.lift_act_ge h]
      rw [List.getElem?_append_right (by lia)] at *; simp
      exact m.act j⟩

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem := congrArg (λ x => x⟨.sub Ty k⟩) h
  have act := @act x T⟨.sub Ty k⟩ $ simp% lem
  by norm_subst [act, <-h]⟩

theorem Typing.rename {Δ Δ' Γ Γ' A t} {r1 : Ren Ty} {r2 : Ren Term}
  (m1 : KindingRen r1 Δ Δ') (m2 : TypingRen r2 Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
| var (x := x) j1 j2 =>
  have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
  var (simp% j1) (j2.rename m1)
| app j1 j2 => app (j1.rename m1 m2) (j2.rename m1 m2)
| lam (A := A) j1 j2 => lam (j1.rename m1) (j2.rename m1 $ m2.lift [A])
| tapp j1 j2 e => tapp (j1.rename m1 m2) (j2.rename m1) (by simp [e])
| tlam j => tlam (simp% j.rename (m1.lift ★) (m2.shift 1))
