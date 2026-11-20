/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TranslateFibers

/-! The bounded square-norm set is partitioned by integer translations.
This constructs a finite norm-curve family. The uniform estimate for the
number of translation classes is a separate lattice theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The quotient of `𝓞 K` by the additive subgroup of rational integers, whose classes are the
orbits under integer translation. -/
abbrev IntegerTranslationQuotient :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples 1

variable (B : ℝ)

/-- The finite set of integer-translation classes of the bounded square-norm integers
`boundedSquareNormIntegers K B`. -/
def boundedSquareNormTranslationClasses :
    Finset (IntegerTranslationQuotient K) := by
  classical
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    (fun α : 𝓞 K ↦ α)

end
end CCDN
