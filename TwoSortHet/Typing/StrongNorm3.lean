import LeanSubst
import TwoSortHet.Typing
import TwoSortHet.Typing.Substitute
import TwoSortHet.Kinding.StrongNorm
import TwoSortHet.Kinding.Value
import TwoSortHet.Reduction
import TwoSortHet.Model
open LeanSubst

namespace TwoSortHet
--naively following lean-sysf/OneSortHomArityGen/StrongNorm2.lean
def SnModelSet := Term -> Prop
def SnRedModelSet := Term -> Term -> Prop
