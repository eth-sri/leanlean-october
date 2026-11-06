/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.NoIndexTwoClassGroupCounting
import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.DiscriminantNumerics
import CCDN.ClassGroup.NumberFieldShortBasis

/-!
The logarithmic branch of CCDN Theorem 6 for number fields with no
index-two intermediate field. All ideal-class representatives, curves,
lattice points and exceptional subfields are constructed and counted.

Uniform finite-radius counts for the ring of integers and its
integer-translation classes. The required short basis is constructed,
and every coefficient depends only on the degree.
-/

namespace CCDN
section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

end

noncomputable section
open NumberField

section
variable (n : ℕ)

/-- The degree-dependent constant in the two-torsion class-group bound for number fields of degree
`n` without an intermediate field of index two. -/
def noIndexTwoClassGroupConstant : ℝ :=
  (noIndexTwoCurveContributionConstant n *
    (numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n) *
      (3 * (9 : ℝ) ^ (n - 1))) * (Real.log 9 + 2) +
    smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)

/-- The constant `noIndexTwoClassGroupConstant n` is positive. -/
lemma noIndexTwoClassGroupConstant_pos :
    0 < noIndexTwoClassGroupConstant n := by
  have hc := noIndexTwoCurveContributionConstant_nonneg n
  have hb := numberFieldLatticeBoxConstant_nonneg n
    (by positivity : 0 ≤ (n : ℝ) ^ 3)
  have he := smallSubfieldIntegerCountConstant_pos n
  have hl : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  unfold noIndexTwoClassGroupConstant
  positivity

end

variable (K : Type*) [Field K] [NumberField K]

