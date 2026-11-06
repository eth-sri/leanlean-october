module
public import GafniTao.HeathBrownNuMoments
public import GafniTao.FordVinogradovMomentMonotone

@[expose] public section

/-!
# The polynomial Weyl moment in Heath-Brown Lemma 1

The source polynomial `S(x; alpha)` has degrees `1, ..., k-1`.  At an
integer cutoff `Q` it is exactly Ford's complete Weyl sum.  Its `2s` moment
is therefore the concrete Vinogradov solution count, and monotonicity permits
the replacement `Q <= H` used in the source.
-/

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

abbrev heathBrownWeylSum (k Q : ℕ)
    (α : HeathBrownCoefficientTorus k) : ℂ :=
  fordVinogradovWeylSum (k - 1) Q α


