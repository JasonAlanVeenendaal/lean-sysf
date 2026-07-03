
import TwoSortHet.Util
import TwoSortHet.Term
open LeanSubst

namespace TwoSortHet

-- inductive Ty.Red : Ty -> Ty -> Prop where
-- | beta {K : Kind} : Ty.Red ((λ[K] b) • t) b[su t::+0]
-- | lam_congr : Ty.Red t t' -> Ty.Red (λ[K1] t) (λ[K1] t') --??
-- | app_congr1 : Ty.Red f f' -> Ty.Red (f • a) (f' • a)
-- | app_congr2 : Ty.Red a a' -> Ty.Red (f • a) (f • a')
-- | all_congr : Ty.Red P P' -> Ty.Red (∀[K1] P) (∀[K1] P') --??
-- | arrow_congr1 : Ty.Red A A' -> Ty.Red (A -:> B) (A' -:> B)
-- | arrow_congr2 : Ty.Red B B' -> Ty.Red (A -:> B) (A -:> B')

-- infix:160 " ~t> " => Ty.Red
-- infix:160 " ~t>* " => Star Ty.Red
-- infix:160 " =t= " => Conv Ty.Red

-- theorem Ty.Red.all_star : V ~t>* P -> (∀[K] V) ~t>* (∀[K] P)
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (all_star h1) (Star.step .refl (Ty.Red.all_congr h2))

-- theorem Ty.Red.lam_star : V ~t>* P -> (λ[A] V) ~t>* (λ[A] P)
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (lam_star h1) (Star.step .refl (Ty.Red.lam_congr h2))

-- theorem Ty.Red.arrow_star1 : A ~t>* A' -> (A -:> B) ~t>* (A' -:> B)
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (arrow_star1 h1) (Star.step .refl (Ty.Red.arrow_congr1 h2))

-- theorem Ty.Red.arrow_star2 : B ~t>* B' -> (A -:> B) ~t>* (A -:> B')
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (arrow_star2 h1) (Star.step .refl (Ty.Red.arrow_congr2 h2))

-- theorem Ty.Red.arrow_star : A ~t>* A' -> B ~t>* B' -> (A -:> B) ~t>* (A' -:> B')
-- | h1, h2 => Star.trans (arrow_star1 h1) (arrow_star2 h2)

-- theorem Ty.Red.app_star1 : A ~t>* A' -> (A • B) ~t>* (A' • B)
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (app_star1 h1) (Star.step .refl (Ty.Red.app_congr1 h2))

-- theorem Ty.Red.app_star2 : B ~t>* B' -> (A • B) ~t>* (A • B')
-- | Star.refl => .refl
-- | Star.step h1 h2 => Star.trans (app_star2 h1) (Star.step .refl (Ty.Red.app_congr2 h2))

-- theorem Ty.Red.app_star : A ~t>* A' -> B ~t>* B' -> (A • B) ~t>* (A' • B')
-- | h1, h2 => Star.trans (app_star1 h1) (app_star2 h2)

-- theorem Ty.Red.all_reduction : (∀[K] P) ~t>* V -> (∃ P', V = (∀[K] P') ∧ (P ~t>* P'))
-- | .refl => ⟨P, ⟨rfl, .refl⟩⟩
-- | .step (y := V') h1 h2 =>
--   have ⟨P', lem1, lem2⟩ := Ty.Red.all_reduction h1
--   match h2 with
--   | .all_congr (P' := P'') j1 => ⟨P'',
--    by injection lem1 with e1 e2; subst e1; apply And.intro; apply rfl; rw [e2] at j1; apply Star.step; apply lem2; apply j1⟩

-- theorem Ty.Red.star_conv : t ~t>* t' -> t =t= t'
-- | .refl => .refl
-- | .step h1 h2 =>
--   let lem := star_conv h1
--   let lem2 := Conv.sym lem
--   let lem3 := Conv.forward lem2 h2
--   Conv.sym lem3

-- instance : HasConfluence Ty.Red where
--   confluence := sorry

-- instance : Substitutive Ty.Red where
--   subst := sorry

end TwoSortHet
