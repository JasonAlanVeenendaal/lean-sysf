import LeanSubst
import OneSortHomArityGen.Term
import OneSortHomArityGen.Reduction
import OneSortHomArityGen.Progress

open LeanSubst

theorem SN.var : SN Red #0 := by
  apply SN.sn; intro y r; cases r

theorem SN.monotone {t : Term} (r : Ren) : SN Red t -> SN Red t[r] := by
  intro h; induction h generalizing r; case _ t h ih =>
  apply SN.sn; intro y h2
  replace h2 := Red.antirename r h2
  rcases h2 with ⟨z, h2, h3⟩; subst h3
  apply ih _ h2
