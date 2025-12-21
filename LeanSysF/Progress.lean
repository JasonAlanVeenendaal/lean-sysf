import LeanSubst
import LeanSysF.Term
import LeanSysF.Kinding
import LeanSysF.Typing
import LeanSysF.Reduction

open LeanSubst

@[simp]
def Term.is_lam : Term -> Bool
| .bind .lam _ _ => true
| _ => false

@[simp]
def Term.is_tlam : Term -> Bool
| .bind .tlam _ _ => true
| _ => false

inductive Value : Term -> Prop where
| var : Value #x
| ctor {ts : Fin v.arity -> Term} :
  ((h : v = .app) -> !(ts (by subst h; exact 0)).is_lam) ->
  ((h : v = .tapp) -> !(ts (by subst h; exact 0)).is_tlam) ->
  (∀ i, Value (ts i)) ->
  Value (.ctor v ts)
| bind {ts : Fin v.arity -> Term} :
  (∀ i, Value (ts i)) ->
  Value t ->
  Value (.bind v ts t)

theorem Value.mk1 : Value t -> ∀ (a : Fin 1), Value (mk1 t a) := by
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
  case ctor v ts j1 j2 j3 ih =>
    intro t' r
    cases r
    case _ => simp at j1
    case _ => simp at j2
    case _ i ts' h r => apply ih i _ r
  case bind t v ts j1 j2 ih1 ih2 =>
    intro t' r
    cases r
    case _ i ts' h r => apply ih1 i _ r
    case _ t' r => apply ih2 _ r

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
              rw [<-mk2_eta (t := ts)]
              rw [zdef, adef]
              rw [<-mk1_eta (t := ts')]
              apply Red.beta
            all_goals solve | (
              apply Or.inl; apply Value.ctor
              simp; rw [zdef]; simp
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
              rw [<-mk2_eta (t := ts)]
              rw [zdef, adef]; simp
              apply Red.tbeta
            all_goals solve | (
              apply Or.inl; apply Value.ctor
              simp; simp; rw [zdef]
              apply Value.mk2 ih1 ih2)
          all_goals solve | (
            rw [zdef] at ih1
            apply Or.inl
            apply Value.ctor
            simp; simp; rw [zdef]
            simp [*])
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
          apply Red.bind2 r
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
        apply Red.bind2 r
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
        apply Red.bind2 r
