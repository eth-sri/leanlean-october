/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/

import GaussianFields.LogCorrelated.ABK.CanonicalField

/-!
# GaussianFields ABK annular field

Port of the corresponding GaussianFields source module.
-/


open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Annular shell kernels -/

/-- The annular interval `[a,b]` in the scale variable, implemented as an indicator on the product
kernel.  ABK uses `a = 3^{n-1}` and `b = 3^n`. -/

noncomputable def abkAnnularLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) :
    ℝ × Vec d → ℝ :=
  (abkScaleShell (d := d) a b).indicator (abkLogKernelProd normalization ζ ψ)

@[simp]
theorem abkAnnularLogKernelProd_apply {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) (p : ℝ × Vec d) :
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

/-- The annular ABK kernel on concrete scale-space. -/

noncomputable def abkAnnularLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) :
    ScaleSpace d → ℝ :=
  abkAnnularLogKernelProd normalization ζ ψ a b ∘ scaleSpaceMeasurableEquiv d

theorem memLp_abkAnnularLogKernel_of_prod {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d} {a b : ℝ}
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkAnnularLogKernel normalization ζ ψ a b) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkAnnularLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)

/-- The annular `L²(R^{1+d})` vector sent into white noise. -/

noncomputable def abkAnnularLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ)
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hprod).toLp
    (abkAnnularLogKernel normalization ζ ψ a b)

/-- The ABK annular shell contribution, tested against `ψ`. -/

noncomputable def abkAnnularLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ)
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  scaleSpaceWhiteNoiseL2 d (abkAnnularLogKernelLp normalization ζ ψ a b hprod)

end GaussianFields

