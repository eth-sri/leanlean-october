/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/

import GaussianFields.LogCorrelated.ABK.Annular

/-!
# GaussianFields ABK triadic field

Port of the corresponding GaussianFields source module.
-/


open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Triadic ABK shells -/

/-- The ABK triadic scale shell `(3^{n-1}, 3^n]`. -/

def abkTriadicScaleShell (n : ℤ) : Set ℝ :=
  Set.Ioc ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

noncomputable instance instDecidableMem_abkTriadicScaleShell (n : ℤ) (r : ℝ) :
    Decidable (r ∈ abkTriadicScaleShell n) := by
  unfold abkTriadicScaleShell
  infer_instance

/-- The `n`th ABK triadic product-coordinate shell kernel. -/

noncomputable def abkTriadicLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ) :
    ℝ × Vec d → ℝ :=
  abkAnnularLogKernelProd normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

/-- The `n`th ABK triadic shell kernel on concrete scale-space. -/

noncomputable def abkTriadicLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ) :
    ScaleSpace d → ℝ :=
  abkAnnularLogKernel normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

/-- The `n`th ABK triadic `L²(R^{1+d})` kernel. -/

noncomputable def abkTriadicLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ)
    (hprod :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  abkAnnularLogKernelLp normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n) hprod

/-- The `n`th ABK triadic shell contribution, tested against `ψ`. -/

noncomputable def abkTriadicLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ)
    (hprod :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  abkAnnularLogCorrelatedFieldL2 normalization ζ ψ
    ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n) hprod

end GaussianFields

