/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Annular

/-!
# GaussianFields ABK triadic field

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Triadic ABK shells -/

/-- The ABK triadic scale shell `(3^{n-1}, 3^n]`. -/
@[expose]
def abkTriadicScaleShell (n : ℤ) : Set ℝ :=
  Set.Ioc ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

noncomputable instance instDecidableMem_abkTriadicScaleShell (n : ℤ) (r : ℝ) :
    Decidable (r ∈ abkTriadicScaleShell n) := by
  unfold abkTriadicScaleShell
  infer_instance





end GaussianFields

end
