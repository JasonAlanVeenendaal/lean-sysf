
import LeanSubst
import LeanSubst.Reduction
import OneSortHomArityGen.Term

open LeanSubst

inductive Red : Term -> Term -> Prop where
| beta {A b t : Term} : Red ((:λ[A] b) :@ t) (b[su t::+0])
| tbeta {b t : Term} : Red ((Λ b) :@[t]) (b[su t::+0])
| ctor v i {ts ts'} :
  (∀ j ≠ i, ts j = ts' j) ->
  Red (ts i) (ts' i) ->
  Red (.ctor v ts) (.ctor v ts')
| bind1 v i {ts ts' t} :
  (∀ j ≠ i, ts j = ts' j) ->
  Red (ts i) (ts' i) ->
  Red (.bind v ts t) (.bind v ts' t)
| bind2 v {ts t t'} :
  Red t t' ->
  Red (.bind v ts t) (.bind v ts t')

infix:80 " ~> " => Red
infix:81 " ~>* " => Star Red
infix:80 " ~>a " => ActionRed Red

@[app_unexpander Star]
def unexpandStar_Red : Lean.PrettyPrinter.Unexpander
| `($_ Red $s $t) => `($s ~>* $t)
| _ => throw ()

@[app_unexpander ActionRed]
def unexpandActionRed_Red : Lean.PrettyPrinter.Unexpander
| `($_ Red $s $t) => `($s ~>a $t)
| _ => throw ()

theorem Red.antirename {s t : Term} (r : Ren) :
  s[r] ~> t ->
  ∃ z, s ~> z ∧ t = z[r]
:= by
  intro h
  generalize wdef : s[r:Term] = w at *
  induction h generalizing s r
  case beta A b t =>
    cases s <;> simp at wdef
    case ctor n v ts =>
    rcases wdef with ⟨e1, e2, e3⟩
    subst e1; subst e2; simp at *
    rcases e3 with ⟨e3, e4⟩; subst e4
    generalize wdef : ts 0 = w at *
    cases w <;> simp at e3
    case _ n v ts' t =>
    rcases e3 with ⟨e3, e4, e5, e6⟩
    subst e3; subst e4; simp at *
    subst e5; subst e6; simp
    exists (t[su (ts 1)::+0]); apply And.intro
    rw [<-Vec.eta2 ts, wdef]; simp
    rw [<-Vec.eta1 ts']; apply Red.beta
    simp
  case tbeta b t =>
    cases s <;> simp at wdef
    case ctor n v ts =>
    rcases wdef with ⟨e1, e2, e3⟩
    subst e1; subst e2; simp at e3
    rcases e3 with ⟨e3, e4⟩; subst e4
    generalize wdef : ts 0 = w at *
    cases w <;> simp at e3
    case _ n v ts' t =>
    rcases e3 with ⟨e3, e4, e5, e6⟩
    subst e3; subst e4; simp at *
    subst e6; simp
    exists (t[su (ts 1)::+0]); apply And.intro
    rw [<-Vec.eta2 ts, wdef]; simp; apply Red.tbeta
    simp
  case ctor x v i ts ts' j1 j2 ih =>
    cases s <;> simp at wdef
    case _ n v' ts'' =>
    rcases wdef with ⟨e1, e2, e3⟩; subst e1; simp at *
    subst e2; subst e3; simp at *
    replace ih := @ih (ts'' i) r rfl
    rcases ih with ⟨z, h1, h2⟩
    exists (.ctor v' (Vec.update i z ts'')); simp
    apply And.intro
    apply Red.ctor v' i
    apply Vec.update_stable; simp
    simp; apply h1
    funext; case _ j =>
    cases decEq j i
    case _ h3 => rw [Vec.update_neq j h3]; simp [*]
    case _ h3 => subst h3; simp [*]
  case bind1 x v i ts ts' t j1 j2 ih =>
    cases s <;> simp at wdef
    case _ n v' ts'' t' =>
    rcases wdef with ⟨e1, e2, e3, e4⟩
    subst e1; subst e2; simp at *; subst e3; subst e4
    replace ih := @ih (ts'' i) r rfl
    rcases ih with ⟨z, h1, h2⟩
    exists (.bind v' (Vec.update i z ts'') t'); simp
    apply And.intro
    apply Red.bind1 v' i
    apply Vec.update_stable; simp
    simp; apply h1
    funext; case _ j =>
    cases decEq j i
    case _ h3 => rw [Vec.update_neq j h3]; simp [*]
    case _ h3 => subst h3; simp [*]
  case bind2 x v ts t t' j ih =>
    cases s <;> simp at wdef
    case _ i v' ts' t'' =>
    rcases wdef with ⟨e1, e2, e3, e4⟩
    subst e1; subst e2; simp at e3; subst e3; subst e4
    replace ih := @ih t'' (r.lift)
    rw [Ren.to_lift (S := Term)] at ih; simp at ih
    rcases ih with ⟨z, h1, h2⟩
    exists (Term.bind v' ts' z); apply And.intro
    apply Red.bind2 _ h1; subst h2; simp
    rw [Ren.to_lift (S := Term)]; simp

theorem Red.ctor_star_lemma {ts ts'} i :
  (∀ j ≠ i, ts j = ts' j) ->
  ts i ~>* ts' i ->
  .ctor v ts ~>* .ctor v ts'
:= by
  intro h1 r
  generalize sdef : ts i = s at *
  generalize tdef : ts' i = t at *
  induction r generalizing ts ts' i
  case _ =>
    have lem : ts = ts' := by
      funext; case _ x =>
      cases decEq x i with
      | isFalse h3 => apply h1 _ h3
      | isTrue h3 => rw [h3, sdef, tdef]
    rw [lem]; apply Star.refl
  case _ y z r1 r2 ih =>
    subst sdef; subst tdef
    replace ih := @ih ts (Vec.update i y ts') i (Vec.update_stable _ _ h1) rfl Vec.update_eq
    apply Star.step ih
    apply Red.ctor v i Vec.update_neq; simp; exact r2

theorem Red.ctor_star {ts ts' : Vec Term n}:
  (∀ i, ts i ~>* ts' i) ->
  .ctor v ts ~>* .ctor v ts'
:= by
  intro h
  cases v <;> simp at *
  case star => apply Star.refl
  all_goals
    rw [<-Vec.eta2 ts, <-Vec.eta2 ts']
    apply Star.trans
    apply Red.ctor_star_lemma (ts' := v[ts' 0, ts 1]) 0 _ _
    simp; apply h.1; simp
    apply Red.ctor_star_lemma 1 _ _
    simp; apply h.2

theorem Red.bind1_star_lemma {ts ts'} i :
  (∀ j ≠ i, ts j = ts' j) ->
  ts i ~>* ts' i ->
  .bind v ts t ~>* .bind v ts' t
:= by
  intro h r
  generalize udef : ts i = u at *
  generalize wdef : ts' i = w at *
  induction r generalizing ts ts' i
  case _ =>
    have lem : ts = ts' := by
      funext; case _ x =>
      cases decEq x i with
      | isFalse h3 => apply h _ h3
      | isTrue h3 => rw [h3, udef, wdef]
    rw [lem]; apply Star.refl
  case _ v y z r1 r2 ih =>
    subst udef; subst wdef
    replace ih := @ih ts (Vec.update i y ts') i (Vec.update_stable _ _ h) rfl Vec.update_eq
    apply Star.step ih
    apply Red.bind1 v i Vec.update_neq; simp; exact r2

theorem Red.bind2_star_lemma {t t'} :
  t ~>* t' ->
  .bind v ts t ~>* .bind v ts t'
:= by
  intro r
  induction r
  case _ => apply Star.refl
  case _ y z r1 r2 ih =>
    apply Star.step ih
    apply Red.bind2 _ r2

theorem Red.bind_star {ts ts' : Vec Term n}:
  (∀ i, ts i ~>* ts' i) ->
  t ~>* t' ->
  .bind v ts t ~>* .bind v ts' t'
:= by
  intro r1 r2
  cases v <;> simp at *
  case lam =>
    rw [<-Vec.eta1 ts, <-Vec.eta1 ts']
    apply Star.trans; apply Red.bind2_star_lemma r2
    apply Red.bind1_star_lemma 0; simp; simp; apply r1
  all_goals apply Red.bind2_star_lemma r2

theorem Red.subst {t t'} (σ : Subst Term) :
  t ~> t' ->
  t[σ] ~> t'[σ]
:= by
  intro h
  induction h generalizing σ
  case beta A b t =>
    simp; have lem := @Red.beta A[σ] (b[.re 0 :: σ ∘ +1]) (t[σ])
    simp at lem; apply lem
  case tbeta b t =>
    simp; have lem := @Red.tbeta (b[.re 0 :: σ ∘ +1]) (t[σ])
    simp at lem; apply lem
  case ctor v i ts ts' h r ih =>
    simp; apply Red.ctor _ i
    intro j e; rw [h j e]
    apply ih σ
  case bind1 v i ts ts' t h1 h2 ih =>
    simp; apply Red.bind1 _ i
    intro j e; rw [h1 j e]
    apply ih σ
  case bind2 r ih =>
    simp; apply Red.bind2
    replace ih := ih σ.lift; simp at ih
    apply ih

theorem Red.subst_action_lift {σ τ : Subst Term} :
  (∀ i, σ i ~>a τ i) ->
  ∀ i, σ.lift i ~>a τ.lift i
:= by
  intro h i
  cases i <;> simp
  apply ActionRed.re
  case _ x =>
  simp [Subst.compose]
  replace h := h x
  generalize udef : σ x = u at *
  generalize vdef : τ x = v at *
  cases h <;> simp
  case _ r => apply ActionRed.su; apply Red.subst _ r
  case _ => apply ActionRed.re

theorem Red.subst_action (σ τ : Subst Term) :
  (∀ i, σ i ~>a τ i) ->
  t[σ] ~>* t[τ]
:= by
  intro h
  induction t generalizing σ τ <;> simp
  case var x =>
    replace h := h x
    generalize adef : σ x = a at *
    generalize bdef : τ x = b at *
    cases h <;> simp
    case _ r => apply Star.step Star.refl r
    case _ => apply Star.refl
  case ctor v ts ih =>
    apply Red.ctor_star
    intro i; apply ih i _ _ h
  case bind v ts' t ih1 ih2 =>
    apply Red.bind_star
    intro i; apply ih1 i _ _ h
    replace ih2 := ih2 σ.lift τ.lift (Red.subst_action_lift h)
    simp at ih2; apply ih2

theorem Red.app1 : f ~> f' -> (f :@ a) ~> (f' :@ a) := by
  intro r; apply Red.ctor .app 0 _
  apply r
  intro j h
  cases j; case _ v p =>
  cases v <;> simp at *
  case _ j =>
  cases j; simp
  omega

theorem Red.app_inv :
  (f:@ a) ~> t ->
    (∃ A b, (f = :λ[A] b) ∧ t = b[su a::+0])
    ∨ (∃ f', t = f':@ a ∧ f ~> f')
    ∨ (∃ a', t = f :@ a' ∧ a ~> a')
:= by
  intro r; generalize zdef : (f:@ a) = z at r
  cases r <;> simp at zdef
  case beta A b t =>
    cases zdef; case _ e1 e2 =>
    subst e1; subst e2
    apply Or.inl; simp
    exists A; exists b
  case ctor v i ts ts' r1 r2 =>
    rcases zdef with ⟨e1, e2, e3⟩
    subst e1; subst e2; simp at e3
    rcases e3 with ⟨e3, e4⟩; subst e3; subst e4
    cases i using Fin.cases2
    case _ =>
      apply Or.inr; apply Or.inl
      exists (ts' 0); simp [*]
    case _ =>
      apply Or.inr; apply Or.inr
      exists (ts' 1); simp [*]

theorem Red.tapp1 : f ~> f' -> (f :@[a]) ~> (f' :@[a]) := by
  intro r; apply Red.ctor .tapp 0 _
  apply r; intro j h
  cases j using Fin.cases2
  case _ => exfalso; apply h rfl
  case _ => simp

theorem Red.tapp_inv :
  (f:@[a]) ~> t ->
    (∃ b, (f = Λ b) ∧ t = b[su a::+0])
    ∨ (∃ f', t = f':@[a] ∧ f ~> f')
    ∨ (∃ a', t = f :@[a'] ∧ a ~> a')
:= by
  intro r; generalize zdef : (f:@[a]) = z at r
  cases r <;> simp at zdef
  case tbeta b t =>
    rcases zdef with ⟨e1, e2⟩
    subst e1 e2; apply Or.inl
    exists b
  case ctor n v i ts ts' h r =>
    rcases zdef with ⟨e1, e2, e3⟩
    subst e1 e2 e3
    cases i using Fin.cases2 <;> simp at *
    apply Or.inr; apply Or.inl
    subst h; exists ts' 0
    apply Or.inr; apply Or.inr
    subst h; exists ts' 1

theorem Red.lam_inv :
  (:λ[A] b) ~> t ->
    (∃ A', (t = :λ[A'] b) ∧ A ~> A')
    ∨ (∃ b', (t = :λ[A] b') ∧ b ~> b')
:= by
  intro r; generalize zdef : (:λ[A] b) = z at r
  cases r <;> simp at zdef
  case bind1 n v i ts ts' t h r =>
    rcases zdef with ⟨e1, e2, e3, e4⟩
    subst e1 e2 e3 e4
    cases i using Fin.cases1; simp at *
    apply Or.inl r
  case bind2 n v ts t t' r =>
    rcases zdef with ⟨e1, e2, e3, e4⟩
    subst e1 e2 e3 e4
    apply Or.inr; exists t'

theorem Red.tlam_inv : (Λ b) ~> t -> (∃ b', (t = Λ b') ∧ b ~> b') := by
  intro r; generalize zdef : (Λ b) = z at r
  cases r <;> simp at zdef
  case bind1 n v i ts ts' t h r =>
    rcases zdef with ⟨e1, e2, e3, e4⟩
    subst e1 e2 e3 e4
    apply Fin.elim0 i
  case bind2 n v ts t t' r =>
    rcases zdef with ⟨e1, e2, e3, e4⟩
    subst e1 e2 e3 e4; exists t'

instance : Substitutive Red where
  subst := Red.subst

-- inductive ParRed : Term -> Term -> Prop where
-- | star : ParRed ★ ★
-- | var {x} : ParRed (#x) (#x)
-- | arr {A B} : ParRed (A -:> B) (A -:> B)
-- | all {P} : ParRed (:∀ P) (:∀ P)
-- | beta {A b b' t t'} :
--   ParRed b b' ->
--   ParRed t t' ->
--   ParRed ((:λ[A] b) :@ t) (b'[.su t'::I])
-- | app {f f' a a'} :
--   ParRed f f' ->
--   ParRed a a' ->
--   ParRed (f :@ a) (f' :@ a')
-- | lam {A A' t t'} :
--   ParRed A A' ->
--   ParRed t t' ->
--   ParRed (:λ[A] t) (:λ[A'] t')

-- infix:80 " ~p> " => ParRed
-- infix:81 " ~p>* " => Star ParRed

-- inductive ParRedSubstAction : Subst.Action Term -> Subst.Action Term -> Prop where
-- | su {t t'} : t ~p> t' -> ParRedSubstAction (.su t) (.su t')
-- | re {x} : ParRedSubstAction (.re x) (.re x)

-- infix:80 " ~ps> " => ParRedSubstAction
-- infix:81 " ~ps>* " => Star ParRedSubstAction

-- namespace ParRed
--   theorem refl {t} : t ~p> t := by
--     induction t
--     case star => apply ParRed.star
--     case arr => apply ParRed.arr
--     case all => apply ParRed.all
--     case var => apply ParRed.var
--     case app ih1 ih2 => apply ParRed.app ih1 ih2
--     case lam ih => apply ParRed.lam ih

--   @[simp]
--   def complete : Term -> Term
--   | .app (.lam _ b) t =>
--     let b' := complete b
--     let t' := complete t
--     b'[.su t'::I]
--   | .app f a =>
--     let f' := complete f
--     let a' := complete a
--     .app f' a'
--   | .lam A t => .lam A (complete t)
--   | .var k x => .var k x
--   | .star => .star
--   | .arr A B => .arr A B
--   | .all P => .all P

--   theorem subst {t t'} (σ : Subst Term) :
--     t ~p> t' ->
--     t[σ] ~p> t'[σ]
--   := by
--     intro h
--     induction h generalizing σ
--     case star => sorry
--     case arr => sorry
--     case all => sorry
--     case var => apply ParRed.refl
--     case beta A b b' t t' r1 r2 ih1 ih2 =>
--       simp; have lem1 := @ParRed.beta A
--         (b[.re 0 :: σ ∘ S]) (b'[.re 0 :: σ ∘ S])
--         (t[σ]) (t'[σ])
--       simp at lem1; apply lem1
--       apply ih1; apply ih2
--     case app r1 r2 ih1 ih2 =>
--       simp; apply ParRed.app
--       apply ih1; apply ih2
--     case lam r ih =>
--       simp; apply ParRed.lam; apply ih

--   theorem subst_action {x} {σ σ' : Subst Term} (r : Ren) :
--     σ x ~ps> σ' x ->
--     (σ ∘ r.to) x ~ps> (σ' ∘ r.to) x
--   := by
--     intro h
--     unfold Subst.compose; simp
--     generalize zdef : σ x = z at *
--     generalize zpdef : σ' x = z' at *
--     cases z <;> cases z'
--     all_goals (cases h; try simp [*])
--     apply ParRedSubstAction.re
--     case _ r =>
--       apply ParRedSubstAction.su
--       apply subst _ r

--   theorem subst_red_lift {σ σ' : Subst Term} :
--     (∀ x, σ x ~ps> σ' x) ->
--     ∀ x, σ.lift x ~ps> σ'.lift x
--   := by
--     intro h x
--     cases x <;> simp
--     case _ => apply ParRedSubstAction.re
--     case _ x =>
--       have lem := subst_action (· + 1) (h x); simp at lem
--       apply lem

--   theorem hsubst {t t'} {σ σ' : Subst Term} :
--     (∀ x, σ x ~ps> σ' x) ->
--     t ~p> t' ->
--     t[σ] ~p> t'[σ']
--   := by
--     intro h1 h2; induction t generalizing t' σ σ'
--     case star => sorry
--     case arr => sorry
--     case all => sorry
--     case var x =>
--       cases h2; simp
--       replace h1 := h1 x
--       generalize zdef : σ x = z at *
--       generalize zpdef : σ' x = z' at *
--       cases z <;> cases z'
--       all_goals (cases h1; try simp [*])
--       apply refl
--     case app f a ih1 ih2 =>
--       cases h2 <;> simp at *
--       case beta A b b' t r1 r2 =>
--         have lem1 := @ParRed.beta A (b[.re 0 :: σ ∘ S]) (b'[.re 0 :: σ' ∘ S]) (a[σ]) (t[σ'])
--         simp at lem1; apply lem1 _
--         apply ih2 h1 r2
--         have lem2 := ih1 h1 (ParRed.lam r1); simp at lem2
--         cases lem2; case _ lem2 =>
--         apply lem2
--       case app f' a' r1 r2 =>
--         apply ParRed.app
--         apply ih1 h1 r1
--         apply ih2 h1 r2
--     case lam t ih =>
--       cases h2; case _ t' h2 =>
--       simp; apply ParRed.lam
--       have lem := @ih t' σ.lift σ'.lift (subst_red_lift h1) h2
--       simp at lem; apply lem

--   theorem triangle {t s} : t ~p> s -> s ~p> complete t := by
--     intro r; induction r <;> simp at *
--     case star => sorry
--     case arr => sorry
--     case all => sorry
--     case var => apply ParRed.refl
--     case beta ih1 ih2 =>
--       apply hsubst
--       intro x; cases x <;> simp
--       apply ParRedSubstAction.su; apply ih2
--       apply ParRedSubstAction.re; apply ih1
--     case app f f' a a' r1 r2 ih1 ih2 =>
--       cases f <;> simp at *
--       case star => sorry
--       case arr => sorry
--       case all => sorry
--       case var => apply ParRed.app ih1 ih2
--       case app => apply ParRed.app ih1 ih2
--       case lam =>
--         cases r1; case _ r1 =>
--         cases ih1; case _ ih1 =>
--         apply ParRed.beta ih1 ih2
--     case lam ih => apply ParRed.lam ih

--   instance : Substitutive ParRed where
--     subst := subst

--   instance : HasTriangle ParRed where
--     complete := complete
--     triangle := triangle
-- end ParRed

-- namespace Red
--   theorem subst {t t'} (σ : Subst Term) :
--     t ~> t' ->
--     t[σ] ~> t'[σ]
--   := by
--     intro h
--     induction h generalizing σ
--     case beta A b t =>
--       simp; have lem1 := @Red.beta A (b[.re 0 :: σ ∘ S]) (t[σ])
--       simp at lem1; apply lem1
--     case app1 ih =>
--       simp; apply Red.app1 (ih σ)
--     case app2 ih =>
--       simp; apply Red.app2 (ih σ)
--     case lam ih =>
--       simp; apply Red.lam
--       apply ih

--   theorem seq_implies_par {t t'} : t ~> t' -> t ~p> t' := by
--     intro h; induction h
--     case beta => apply ParRed.beta ParRed.refl ParRed.refl
--     case app1 r ih => apply ParRed.app ih ParRed.refl
--     case app2 r ih => apply ParRed.app ParRed.refl ih
--     case lam r ih => apply ParRed.lam ih

--   theorem seqs_implies_pars {t t'} : t ~>* t' -> t ~p>* t' := by
--     intro h; induction h
--     case _ => apply Star.refl
--     case _ y z r1 r2 ih =>
--       replace r2 := seq_implies_par r2
--       apply Star.step ih r2

--   theorem par_implies_seqs {t t'} : t ~p> t' -> t ~>* t' := by
--     intro h; induction h
--     case star => sorry
--     case arr => sorry
--     case all => sorry
--     case var => apply Star.refl
--     case beta A b b' q q' r1 r2 ih1 ih2 =>
--       have lem : (:λ[A] b) ~>* (:λ[A] b') := by
--         apply Star.congr1 (Term.lam A) (@Red.lam A) ih1
--       apply Star.trans
--       apply Star.congr2 Term.app Red.app1 Red.app2 lem ih2
--       apply Star.step Star.refl
--       apply Red.beta
--     case app f f' a a' r1 r2 ih1 ih2 =>
--       apply Star.congr2 Term.app Red.app1 Red.app2 ih1 ih2
--     case lam t t' A r ih =>
--       apply Star.congr1 (Term.lam A) (@Red.lam A) ih

--   theorem pars_implies_seqs {t t'} : t ~p>* t' -> t ~>* t' := by
--     intro h; induction h
--     case _ => apply Star.refl
--     case _ y z r1 r2 ih =>
--       replace r2 := par_implies_seqs r2
--       apply Star.trans ih r2

--   theorem confluence {s t1 t2} : s ~>* t1 -> s ~>* t2 -> ∃ t, t1 ~>* t ∧ t2 ~>* t := by
--     intro h1 h2
--     have lem1 := seqs_implies_pars h1
--     have lem2 := seqs_implies_pars h2
--     have lem3 := HasConfluence.confluence lem1 lem2
--     cases lem3; case _ w lem3 =>
--     have lem4 := pars_implies_seqs lem3.1
--     have lem5 := pars_implies_seqs lem3.2
--     exists w

--   instance : Substitutive Red where
--     subst := subst

--   instance : HasConfluence Red where
--     confluence := confluence
-- end Red
