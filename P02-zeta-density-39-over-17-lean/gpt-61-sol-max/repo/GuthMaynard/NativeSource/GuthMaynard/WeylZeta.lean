module
public import GuthMaynard.WeylZeta
public import GuthMaynard.NativeSource.GuthMaynard.WeylExplicit

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  logarithmicSum_eq_sum_range
  norm_weighted_sum_le_of_antitone
)

/-!
# Critical-line consequences of the Weyl estimate

The finite Abel lemma below transfers uniform bounds for unweighted phase
prefixes to monotone nonnegative weights.  It is then applied to the actual
`n^(-1/2-it)` critical-line weight.
-/

end GuthMaynard.NativeMoment
