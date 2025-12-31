
import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding
import OneSortHomArityGen.Typing
import OneSortHomArityGen.Reduction
import OneSortHomArityGen.Progress
import OneSortHomArityGen.SN

open LeanSubst

-- Heavily following Lectures in Curry-Howard and the autosubst work:
--
-- Lectures on the Curry-Howard Isomorphism
-- https://github.com/rocq-community/autosubst/blob/master/examples/ssr/SystemF_SN.v

-- Notable differences:
-- 1. Syntax/substitutions are single-sorted
-- -- The Rocq development uses multisorted syntax/substitutions
-- 2. Reduction is full (in particular we have all congruences rules)
-- -- The Rocq development does not have congruence rules for type-positions
-- 3. [2] forces a restriction on type instantiation; we choose Value
-- 4. [3] forces us to know that A[σ] value when Γ ⊢ A type, which in turn requires that the
--    logial relation is Kripke
-- 5. [4] also requires a 4th property of candidates (monotonicity of renaming)

-- Shallow neutral, turns out to be enough
@[simp]
def Term.not_lam : Term -> Bool
| bind .lam _ _ => false
| bind .tlam _ _ => false
| _ => true

namespace Normalization.Verison1

-- Setup for semantic typing
@[simp]
abbrev Cand := Term -> Prop

structure Reducible (P : Cand) : Prop where
  subset : ∀ {t}, P t -> SN Red t
  closed : ∀ {s t}, P s -> s ~> t -> P t
  neu_acc : ∀ {s}, s.not_lam -> (∀ t, s ~> t -> P t) -> P s
  mono : ∀ {t} (r : Ren), P t -> P t[r]

def Admissible : (Nat -> Cand) -> Prop
| ξ => ∀ x, Reducible (ξ x)

@[simp]
def LR (ξ : Nat -> Cand) : Term -> Cand
| #x => ξ x
| .ctor .arr ts => λ t => ∀ (r:Ren) a, LR ξ (ts 0) a -> LR ξ (ts 1) (t[r] :@ a)
| .bind .all _ P => λ t => ∀ (r:Ren) C a, Reducible C -> Value a -> LR (C::ξ) P (t[r] :@[a])
| _ => λ t => SN Red t

def ΓR (ξ : Nat -> Cand) : Ctx Term -> (Subst Term -> Prop)
| Γ, σ => ∀ x,
  (Γ[x] ≠ ★ -> LR ξ Γ[x] ↑(σ x))
  ∧ (Γ[x] = ★ -> Value (σ x))

@[simp]
def SemanticTyping Γ t A := ∀ ξ σ, Admissible ξ -> ΓR ξ Γ σ -> LR ξ A t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem Reducible.sn : Reducible (SN Red) := by
  constructor
  case _ => simp
  case _ =>
    intro s t h r
    apply SN.preservation_step h r
  case _ =>
    intro s h1 h2
    apply SN.sn h2
  case _ =>
    intro t r h
    apply SN.monotone r h

theorem Admissible.sn : Admissible (λ _ => SN Red) := by
  intro x; apply Reducible.sn

theorem Reducible.var x : Reducible P -> P #x := by
  intro h; apply h.neu_acc; simp
  intro t r; cases r

theorem Reducible.cons : Reducible P -> Admissible ξ -> Admissible (P::ξ) := by
  intro h1 h2 x
  cases x <;> simp [*]
  case _ x => apply h2 x

theorem LR.monotone (r : Ren) : Admissible ξ -> LR ξ A t -> LR ξ A t[r] := by
  intro ad h; cases A
  case var x =>
    simp at *
    apply (ad x).mono r h
  case ctor n v ts =>
    cases v
    case arr =>
      simp at *; intro r' a h1
      replace h := h (r' ∘ r) a h1
      rw [Ren.to_compose] at h; apply h
    all_goals simp at *; apply SN.monotone; apply h
  case bind n v ts b =>
    cases v
    case all =>
      simp at *; intro r' C a h1 h2
      replace h := h (r' ∘ r) C a h1 h2
      rw [Ren.to_compose] at h; apply h
    all_goals simp at *; apply SN.monotone; apply h

theorem LR.reducible A : Admissible ξ -> Reducible (LR ξ A) := by
  intro ad
  induction A generalizing ξ
  case var x => simp; apply ad
  case ctor v ts ih =>
    cases v
    all_goals try solve | simp; apply Reducible.sn
    have ih1 := ih (Fin.ofNat 2 0) ad; simp at ih1
    have ih2 := ih (Fin.ofNat 2 1) ad; simp at ih2
    rw [<-Vec.eta2 (t := ts)]
    constructor
    case subset =>
      intro t q
      have lem := q id #0 (Reducible.var 0 ih1); simp at lem
      replace lem := ih2.subset lem
      apply SN.preimage (· :@ #0) t _ lem
      simp; intro x y
      apply Red.app1
    case closed =>
      intro s t q r re a la
      have lem1 := q re a la
      have lem2 : (s[re] :@ a) ~> (t[re] :@ a) := by
        apply Red.ctor _ 0 <;> simp
        apply Red.subst _ r
      apply ih2.closed lem1 lem2
    case neu_acc =>
      intro s q1 q2 re a la
      have lem := ih1.subset la
      induction lem; case _ x lem ih3 =>
      apply ih2.neu_acc; rfl; intro t r
      replace r := Red.app_inv r
      rcases r with ⟨A, b, e1, e2⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
      case _ =>
        cases s <;> simp at e1
        rcases e1 with ⟨e1, e2, e3, e4⟩
        subst e1; simp at *; subst e2; subst e3; subst e4
        simp at q1
      case _ =>
        subst e
        have lem : ∃ z, s ~> z ∧ f' = z[re] := Red.antirename re r
        rcases lem with ⟨z, h1, h2⟩
        replace q2 := q2 _ h1; simp at q2
        subst h2; apply q2 re x la
      case _ =>
        subst e; apply ih3 _ r
        apply ih1.closed la r
    case mono =>
      intro t r h
      apply LR.monotone r ad; apply h
  case bind v ts A ih1 ih2 =>
    cases v
    all_goals try solve | simp; apply Reducible.sn
    constructor
    case subset =>
      replace ih := @ih2 ((SN Red)::ξ) (Reducible.cons Reducible.sn ad)
      intro t q
      have lem := q id (SN Red) #0 Reducible.sn Value.var; simp at lem
      replace lem := ih.subset lem
      apply SN.preimage (· :@[#0]) t _ lem
      simp; intro x y
      apply Red.tapp1
    case closed =>
      intro s t q1 r re C a q2 q3
      replace ih := @ih2 (C::ξ) (Reducible.cons q2 ad)
      apply ih.closed
      apply q1 re _ a q2 q3
      have lem : s[re] ~> t[re] := by apply Red.subst _ r
      apply Red.tapp1 lem
    case neu_acc =>
      intro s q1 q2 re C a q3 q4
      replace ih := @ih2 (C::ξ) (Reducible.cons q3 ad)
      apply ih.neu_acc; rfl
      intro t r
      replace r := Red.tapp_inv r
      rcases r with ⟨b, e1, e2⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
      case _ =>
        cases s <;> simp at e1
        rcases e1 with ⟨e1, e2, e3, e4⟩
        subst e1; simp at *; subst e2
        simp at q1
      case _ =>
        subst e
        have lem : ∃ z, s ~> z ∧ f' = z[re] := Red.antirename re r
        rcases lem with ⟨z, h1, h2⟩
        replace q2 := q2 _ h1; simp at q2
        subst h2; apply q2 re _ _ q3 q4
      case _ => exfalso; apply Value.sound q4 _ r
    case mono =>
      intro t r h
      apply LR.monotone r ad; apply h

theorem LR.var : Admissible ξ -> LR ξ T #x := by
  intro h
  have lem := LR.reducible T h
  apply lem.neu_acc; rfl
  intro t r; cases r

theorem LR.preservation :
  Admissible ξ ->
  LR ξ T s ->
  s ~>* t ->
  LR ξ T t
:= by
  intro h1 h2 h3
  have lem := LR.reducible T h1
  induction h3; simp [*]
  case _ r1 r2 => apply lem.closed r2 r1

theorem LR.beta_expansion :
  Admissible ξ ->
  SN Red t ->
  Value B ->
  LR ξ A b[su t::+0] ->
  LR ξ A ((:λ[B] b) :@ t)
:= by
  intro ad snt vb h
  have lem := LR.reducible A ad
  have sns := SN.subst_preimage (lem.subset h)
  induction sns generalizing t; case _ s sns ih1 =>
  induction snt; case _ t snt ih2 =>
  apply lem.neu_acc; rfl; intro u r; simp at r
  replace r := Red.app_inv r
  rcases r with ⟨A, b, e, r⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
  case _ =>
    injection e with _ _ _ e
    subst r; subst e; apply h
  case _ =>
    subst e; replace r := Red.lam_inv r
    rcases r with ⟨B', e, r⟩ | ⟨b', e, r⟩
    case _ => exfalso; apply Value.sound vb _ r
    case _ =>
      subst e
      apply ih1 _ r; apply SN.sn snt
      replace r := Substitutive.subst (su t::+0) r
      apply lem.closed h r
  case _ =>
    subst e; apply ih2 _ r
    replace r : s[su t::+0] ~>* s[su a'::+0] := by
      apply Red.subst_action (su t::+0) (su a'::+0)
      intro i; cases i <;> simp
      apply ActionRed.su r
      apply ActionRed.re
    apply LR.preservation ad h r

theorem LR.tbeta_expansion :
  Admissible ξ ->
  Value t ->
  LR ξ A b[su t::+0] ->
  LR ξ A ((Λ b) :@[t])
:= by
  intro ad vt h
  have lem := LR.reducible A ad
  have sns := SN.subst_preimage (lem.subset h)
  induction sns; case _ x h ih =>
  apply lem.neu_acc; rfl; intro s r
  replace r := Red.tapp_inv r
  rcases r with ⟨b, e1, e2⟩ | ⟨f', e, r⟩ | ⟨a', e, r⟩
  case _ =>
    injection e1 with _ _ _ e1; subst e1; subst e2
    apply h
  case _ =>
    subst e; replace r := Red.tlam_inv r
    rcases r with ⟨b', e, r⟩; subst e
    apply ih _ r
    have r2 := Substitutive.subst (su t::+0) r
    apply lem.closed h r2
  case _ => exfalso; apply Value.sound vt _ r

theorem valuation_equiv_lift {ξ ζ : Nat -> Cand} :
  (∀ i t, ξ i t <-> ζ i t) ->
  ∀ P i t, (P::ξ) i t <-> (P::ζ) i t
:= by
  intro h P i t
  cases i <;> simp; rw [h]

theorem LR.valuation_equiv :
  (∀ i t, ξ i t <-> ζ i t) ->
  (LR ξ T t <-> LR ζ T t)
:= by
  intro h1
  induction T generalizing ξ ζ t
  case var x => apply h1
  case ctor v ts ih =>
    cases v <;> simp
    have ih1 := @ih (Fin.ofNat 2 0); simp at ih1
    have ih2 := @ih (Fin.ofNat 2 1); simp at ih2
    apply Iff.intro
    case _ =>
      intro h2 r a h3
      have lem1 := (ih1 h1).2 h3
      replace h2 := h2 r _ lem1
      apply (ih2 h1).1 h2
    case _ =>
      intro h2 r a h3
      have lem1 := (ih1 h1).1 h3
      replace h2 := h2 r _ lem1
      apply (ih2 h1).2 h2
  case bind v ts s ih1 ih2 =>
    cases v <;> simp
    apply Iff.intro
    case _ =>
      intro h2 r C a h3
      replace h2 := h2 r C a h3
      replace ih2 := @ih2 (C::ξ) (C::ζ) (t[r] :@[a])
      rw [<-ih2]; apply h2
      intro i t; cases i <;> simp; rw [h1]
    case _ =>
      intro h2 r C a h3
      replace h2 := h2 r C a h3
      replace ih2 := @ih2 (C::ξ) (C::ζ) (t[r] :@[a])
      rw [ih2]; apply h2
      intro i t; cases i <;> simp; rw [h1]

theorem LR.rename (r : Ren) : LR ξ T[r] t <-> LR (ξ ∘ r) T t := by
  induction T generalizing ξ r t
  case var x => simp
  case ctor v ts ih =>
    cases v <;> simp
    have ih1 := @ih (Fin.ofNat 2 0); simp at ih1
    have ih2 := @ih (Fin.ofNat 2 1); simp at ih2
    apply Iff.intro
    case _ =>
      intro h1 re a h2
      replace h2 := (ih1 r).2 h2
      apply (ih2 r).1; apply h1 re _ h2
    case _ =>
      intro h1 re a h2
      replace h2 := (ih1 r).1 h2
      apply (ih2 r).2; apply h1 re _ h2
  case bind v ts s ih1 ih2 =>
    cases v <;> simp
    apply Iff.intro
    case _ =>
      intro h1 re C a h2 h3
      have lem1 := @ih2 (C::ξ) (t[re] :@[a]) r.lift
      have lem2 : (C::ξ) ∘ r.lift = C::ξ ∘ r := by
        funext; case _ i t =>
        unfold Function.comp
        cases i <;> simp [Ren.lift]
      rw [lem2, Ren.to_lift (S := Term)] at lem1; simp at lem1
      apply lem1.1; apply h1; apply h2; apply h3
    case _ =>
      intro h1 re C a h2 h3
      have lem1 := @ih2 (C::ξ) (t[re] :@[a]) r.lift
      have lem2 : (C::ξ) ∘ r.lift = C::ξ ∘ r := by
        funext; case _ i t =>
        unfold Function.comp
        cases i <;> simp [Ren.lift]
      rw [lem2, Ren.to_lift (S := Term)] at lem1; simp at lem1
      apply lem1.2; apply h1; apply h2; apply h3

theorem LR.weaken : LR (P::ξ) T[+1] t <-> LR ξ T t := by
  exact LR.rename (· + 1)

theorem LR.subst : LR ξ T[σ] t <-> LR (λ i => LR ξ (σ i)) T t := by
  induction T generalizing ξ t
  case var => simp
  case ctor v ts ih =>
    cases v <;> simp
    have ih1 := @ih (Fin.ofNat 2 0); simp at ih1
    have ih2 := @ih (Fin.ofNat 2 1); simp at ih2
    apply Iff.intro
    case _ =>
      intro h1 re a h2
      have lem1 := (@ih1 ξ σ a).2 h2
      replace h1 := h1 re _ lem1
      have lem2 := (@ih2 ξ σ (t[re] :@ a)).1 h1
      apply lem2
    case _ =>
      intro h1 re a h2
      have lem1 := (@ih1 ξ σ a).1 h2
      replace h1 := h1 re _ lem1
      have lem2 := (@ih2 ξ σ (t[re] :@ a)).2 h1
      apply lem2
  case bind v ts s ih1 ih2 =>
    cases v <;> simp
    apply Iff.intro
    case _ =>
      intro h1 k C a h2 h3
      replace h1 := h1 k C a h2 h3
      replace ih2 := @ih2 (C::ξ) σ.lift (t[k] :@[a])
      have lem1 : σ.lift = re 0::σ ∘ +1 := by simp
      rw [lem1] at ih2; rw [ih2] at h1
      rw [LR.valuation_equiv]; apply h1
      intro i t; cases i <;> simp
      case _ i =>
      have lem2 : ↑((σ ∘ +1) i) = (Term.from_action (σ i))[+1] := by simp
      rw [lem2, LR.weaken]
    case _ =>
      intro h1 k C a h2
      replace h1 := h1 k C a h2
      replace ih2 := @ih2 (C::ξ) σ.lift (t[k] :@[a])
      have lem1 : σ.lift = re 0::σ ∘ +1 := by simp
      rw [lem1] at ih2; rw [ih2]
      rw [LR.valuation_equiv]; apply h1
      intro i t; cases i <;> simp
      case _ i =>
      have lem2 : ↑((σ ∘ +1) i) = (Term.from_action (σ i))[+1] := by simp
      rw [lem2, LR.weaken]

theorem Term.succ_not_star_implies_not_star : A[+1] ≠ ★ -> A ≠ ★ := by
  intro h1 h2; subst h2; simp at h1

theorem ΓR.rename (r : Ren) :
  Admissible ξ ->
  ΓR ξ Γ σ ->
  ΓR ξ Γ (σ ∘ r.to)
:= by
  intro ad h1 x
  apply And.intro
  case _ =>
    intro h2
    replace h1 := (h1 x).1 h2
    replace h1 := LR.monotone r ad h1; simp at h1
    apply h1
  case _ =>
    intro h2
    replace h1 := (h1 x).2 h2
    replace h1 := Value.monotone r h1; simp at h1
    apply h1

theorem ΓR.kinding_subst_value :
  Admissible ξ ->
  ΓR ξ Γ σ ->
  Γ ⊢ A type ->
  Value A[σ]
:= by
  intro ad cr j
  induction j generalizing ξ σ
  case var Γ x j => simp; apply (cr x).2 j
  case arr ih1 ih2 =>
    simp; apply Value.ctor; simp
    apply Value.mk2 <;> simp
    apply ih1 ad cr
    apply ih2 ad cr
  case all Γ P j ih =>
    have lem : σ.lift = re 0::σ ∘ +1 := by simp
    replace ih := @ih (SN Red::ξ) σ.lift; rw [lem] at ih
    have lem : ∀ {x}, ↑((σ ∘ +1) x) = (Term.from_action (σ x))[+1] := by simp
    simp; apply Value.bind; simp
    apply ih; apply Reducible.cons Reducible.sn ad
    intro x; apply And.intro _ _
    case _ =>
      intro h; cases x <;> simp
      case _ => apply SN.var
      case _ x =>
        replace h := Term.succ_not_star_implies_not_star h
        replace cr := (cr x).1 h
        rw [LR.weaken]
        rw [lem]; apply LR.monotone _ ad cr
    case _ =>
      intro h; cases x <;> simp; apply Value.var
      case _ x =>
      replace h := Term.ren_eq_star h
      replace cr := (cr x).2 h
      rw [lem]; apply Value.monotone _ cr

theorem fundamental  : Γ ⊢ t : A -> Γ ⊨ t : A := by
  intro j; induction j <;> simp
  case var Γ T x j1 j2 =>
    intro ξ σ h1 h2
    subst j1; apply (h2 x).1
    intro h; rw [h] at j2
    cases j2
  case app Γ A B f a j1 j2 ih1 ih2 =>
    intro ξ σ h1 h2; simp at *
    replace ih1 := ih1 ξ σ h1 h2 id a[σ]; simp at ih1
    apply ih1
    apply ih2 ξ σ h1 h2
  case lam Γ A B t j1 j2 ih =>
    intro ξ σ h1 h2 r a la; simp at *
    replace ih := ih ((SN Red)::ξ) (su a::σ ∘ r.to) (by {
      intro x; cases x <;> simp
      apply Reducible.sn
      apply h1
    }) (by {
      intro x; cases x <;> simp
      case _ =>
        apply And.intro _ _
        case _ => intro h; rw [LR.weaken]; exact la
        case _ =>
          intro h
          replace h := Term.ren_eq_star h
          rw [h] at j1; cases j1
      case _ x =>
        replace h2 := h2 x
        apply And.intro _ _
        case _ =>
          intro h
          replace h := Term.succ_not_star_implies_not_star h
          rw [LR.weaken]
          replace h2 := LR.monotone r h1 (h2.1 h); simp at h2
          apply h2
        case _ =>
          intro h
          replace h := Term.ren_eq_star h
          replace h2 := Value.monotone r (h2.2 h); simp at h2
          apply h2
    }); simp at ih
    have lem1 := LR.reducible A h1
    replace lem1 := lem1.subset la
    have lem2 := ΓR.kinding_subst_value h1 (ΓR.rename r h1 h2) j1
    apply LR.beta_expansion h1 lem1 lem2; simp
    rw [LR.weaken] at ih; apply ih
  case tapp Γ P P' f a j1 j2 j3 ih =>
    intro ξ σ h1 h2; subst j3; simp at ih;
    rw [LR.subst]
    have lem0 : Value a[σ] := ΓR.kinding_subst_value h1 h2 j2
    have lem1 := ih ξ σ h1 h2 id (LR ξ a) a[σ] (LR.reducible a h1) lem0; simp at lem1
    have lem2 : ∀ i t, (LR ξ a::ξ) i t <-> (fun i => LR ξ ↑((su a::+0) i)) i t := by
      intro i t; cases i <;> simp
    apply (LR.valuation_equiv lem2).1 lem1
  case tlam Γ P t j ih =>
    intro ξ σ h1 h2 r C a rc av; simp at ih
    apply LR.tbeta_expansion
    apply Reducible.cons rc h1
    apply av; simp
    apply ih (C::ξ) (su a::σ ∘ r.to)
    intro x; apply Reducible.cons rc h1
    intro x; cases x <;> simp
    case _ => apply av
    case _ x =>
      replace h2 := h2 x
      apply And.intro _ _
      case _ =>
        intro h
        replace h := Term.succ_not_star_implies_not_star h
        rw [LR.weaken]
        replace h2 := LR.monotone r h1 (h2.1 h); simp at h2
        apply h2
      case _ =>
        intro h
        replace h := Term.ren_eq_star h
        replace h2 := Value.monotone r (h2.2 h); simp at h2
        apply h2

theorem strong_normalization : Γ ⊢ t : A -> SN Red t := by
  intro j; have lem1 := fundamental j; simp at lem1
  replace lem1 := lem1 (λ x => SN Red) +0
    (by intro x; apply Reducible.sn) (by {
      intro x; apply And.intro
      case _ =>
        intro h; simp
        apply LR.var
        apply Admissible.sn
      case _ =>
        intro h; simp
        apply Value.var
  })
  simp at lem1
  replace lem2 := LR.reducible A Admissible.sn
  apply lem2.subset lem1


end Normalization.Verison1
