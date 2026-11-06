/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.CanonicalField

/-!
# GaussianFields ABK annular field

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Annular shell kernels -/

variable {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ)

include d normalization ζ ψ a b in
/-- The annular interval `[a,b]` in the scale variable, implemented as an indicator on the product
kernel.  ABK uses `a = 3^{n-1}` and `b = 3^n`. -/
@[expose]
noncomputable def abkAnnularLogKernelProd  :
    ℝ × Vec d → ℝ :=
  (abkScaleShell (d := d) a b).indicator (abkLogKernelProd normalization ζ ψ)

include d normalization ζ ψ a b in
@[simp]
theorem abkAnnularLogKernelProd_apply  (p : ℝ × Vec d) :
    abkAnnularLogKernelProd normalization ζ ψ a b p =
      if p.1 ∈ Set.Ioc a b then
        abkLogKernelProd normalization ζ ψ p
      else
        0 := by
  by_cases hp : p.1 ∈ Set.Ioc a b
  · have hp' : p ∈ abkScaleShell (d := d) a b := hp
    rw [ite_eq_left hp]
    exact Set.indicator_of_mem hp' (abkLogKernelProd normalization ζ ψ)
  · have hp' : p ∉ abkScaleShell (d := d) a b := hp
    rw [ite_eq_right hp]
    exact Set.indicator_of_notMem hp' (abkLogKernelProd normalization ζ ψ)









end GaussianFields

end
