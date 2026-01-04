import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Kinding
import OneSortHomArityGen.Typing
import OneSortHomArityGen.Reduction

namespace OneSortHomArityGen

open LeanSubst

@[simp]
def Term.is_lam : Term -> Bool
| .bind .lam _ _ => true
| _ => false

@[simp]
def Term.is_tlam : Term -> Bool
| .bind .tlam _ _ => true
| _ => false

@[simp]
def ctor_neutral : Variant s n -> Vec Term n -> Bool
| .app, ts => !(ts 0).is_lam
| .tapp, ts => !(ts 0).is_tlam
| _, _ => true

theorem ctor_neutral_monotone (r : Ren)
  : ctor_neutral v ts -> ctor_neutral v (λ i => (ts i)[r])
:= by
  intro h
  cases v <;> simp at *
  all_goals
    generalize zdef : ts 0 = z at *
    cases z <;> simp at *
    case _ v _ _ =>
    cases v <;> simp at *

inductive Value : Term -> Prop where
| var : Value #x
| ctor {ts : Vec Term n} :
  ctor_neutral v ts ->
  (∀ i, Value (ts i)) ->
  Value (.ctor v ts)
| bind {ts : Vec Term n} :
  (∀ i, Value (ts i)) ->
  Value t ->
  Value (.bind v ts t)

theorem Value.mk1 : Value t -> ∀ (a : Fin 1), Value (v[t] a) := by
  intro v a
  cases a; case _ x p =>
  cases x; exact v
  omega

theorem Value.mk2 {ts : Fin 2 -> Term} :
  Value (ts 0) ->
  Value (ts 1) ->
  ∀ (a : Fin 2), Value (ts a)
:= by
  intro v1 v2 a
  cases a; case _ x p =>
  cases x; exact v1; case _ x =>
  cases x; exact v2; case _ x =>
  omega

theorem Value.sound : Value t -> ∀ t', ¬ (t ~> t') := by
  intro h
  induction h
  case var => intro t' r; cases r
  case ctor n v ts j1 j2 ih =>
    intro t' r
    cases r
    case _ => simp at j1
    case _ => simp at j1
    case _ i ts' h r => apply ih i _ r
  case bind t v ts j1 j2 ih1 ih2 =>
    intro t' r
    cases r
    case _ i ts' h r => apply ih1 i _ r
    case _ t' r => apply ih2 _ r

theorem Value.monotone (r : Ren) : Value t -> Value t[r] := by
  intro v; induction v generalizing r <;> simp
  case var => apply Value.var
  case ctor n v ts j1 j2 ih =>
    apply Value.ctor
    rw [ctor_neutral_monotone r j1]
    intro i; apply ih i r
  case bind n t v ts j1 j2 ih1 ih2 =>
    apply Value.bind
    intro i; apply ih1 i r
    replace ih2 := ih2 r.lift
    rw [Ren.to_lift (S := Term)] at ih2; simp at ih2
    apply ih2

theorem Kinding.value : Γ ⊢ A type -> Value A := by
  intro j; induction j
  case var => apply Value.var
  case arr ih1 ih2 =>
    apply Value.ctor
    all_goals simp [*]
  case all ih =>
    apply Value.bind
    all_goals simp [*]

theorem progress t : Value t ∨ (∃ t', t ~> t') := by
  induction t
  case var => apply Or.inl; apply Value.var
  case ctor v ts ih =>
    cases v <;> simp at *
    case _ =>
      apply Or.inl; apply Value.ctor
      all_goals simp
    case _ =>
      cases ih; case _ ih1 ih2 =>
      cases ih1
      case _ ih1 =>
        cases ih2
        case _ ih2 =>
          generalize zdef : ts 0 = z
          cases z
          case bind v ts' t' =>
            cases v
            case lam =>
              apply Or.inr
              generalize adef : ts 1 = a at *
              exists (t'[su a::+0])
              rw [<-Vec.eta2 (t := ts)]
              rw [zdef, adef]
              rw [<-Vec.eta1 (t := ts')]
              apply Red.beta
            all_goals solve | (
              apply Or.inl; apply Value.ctor
              simp; rw [zdef]
              apply Value.mk2 ih1 ih2)
          all_goals solve | (
            rw [zdef] at ih1
            apply Or.inl
            apply Value.ctor
            simp; rw [zdef]
            simp; simp [*])
        case _ ih2 =>
          cases ih2; case _ t' ih2 =>
          apply Or.inr
          exists ((ts 0) :@ t')
          apply Red.ctor (i := 1)
          all_goals simp [*]
      case _ ih1 =>
        cases ih1; case _ t' ih1 =>
        apply Or.inr
        exists (t' :@ (ts 1))
        apply Red.ctor (i := 0)
        all_goals simp [*]
    case _ =>
      cases ih; case _ ih1 ih2 =>
      cases ih1
      case _ ih1 =>
        cases ih2
        case _ ih2 =>
          generalize zdef : ts 0 = z
          cases z
          case bind v ts' t' =>
            cases v
            case tlam =>
              apply Or.inr
              generalize adef : ts 1 = a at *
              exists (t'[su a::+0])
              rw [<-Vec.eta2 (t := ts)]
              rw [zdef, adef]; simp
              apply Red.tbeta
            all_goals solve | (
              apply Or.inl; apply Value.ctor
              simp [*]; apply Value.mk2 ih1 ih2)
          all_goals solve | (
            rw [zdef] at ih1
            apply Or.inl
            apply Value.ctor
            simp [*]; simp [*])
        case _ ih2 =>
          cases ih2; case _ t' ih2 =>
          apply Or.inr
          exists ((ts 0) :@[t'])
          apply Red.ctor (i := 1)
          all_goals simp [*]
      case _ ih1 =>
        cases ih1; case _ t' ih1 =>
        apply Or.inr
        exists (t' :@[ts 1])
        apply Red.ctor (i := 0)
        all_goals simp [*]
    case _ =>
      cases ih; case _ ih1 ih2 =>
      cases ih1
      case _ ih1 =>
        cases ih2
        case _ ih2 =>
          apply Or.inl
          apply Value.ctor
          all_goals simp [*]
        case _ ih2 =>
          cases ih2; case _ t' r =>
          apply Or.inr
          exists ((ts 0) -:> t')
          apply Red.ctor (i := 1)
          all_goals simp [*]
      case _ ih1 =>
        cases ih1; case _ t' r =>
        apply Or.inr
        exists (t' -:> (ts 1))
        apply Red.ctor (i := 0)
        all_goals simp [*]
  case bind v ts t ih1 ih2 =>
    cases v <;> simp at *
    case _ =>
      cases ih1
      case _ ih1 =>
        cases ih2
        case _ ih2 =>
          apply Or.inl
          apply Value.bind
          all_goals simp [*]
        case _ ih2 =>
          cases ih2; case _ t' r =>
          apply Or.inr
          exists (:λ[ts 0] t'); simp
          apply Red.bind2 _ r
      case _ ih1 =>
        cases ih1; case _ t' r =>
        apply Or.inr
        exists (:λ[t'] t)
        apply Red.bind1 (i := 0)
        all_goals simp [*]
    case _ =>
      cases ih2
      case _ ih2 =>
        apply Or.inl
        apply Value.bind
        all_goals simp [*]
      case _ ih2 =>
        cases ih2; case _ t' r =>
        apply Or.inr
        exists (Λ t')
        apply Red.bind2 _ r
    case _ =>
      cases ih2
      case _ ih2 =>
        apply Or.inl
        apply Value.bind
        all_goals simp [*]
      case _ ih2 =>
        cases ih2; case _ t' r =>
        apply Or.inr
        exists (:∀ t')
        apply Red.bind2 _ r

end OneSortHomArityGen
