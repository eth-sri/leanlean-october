/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.KernelLimitContinuity
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import GaussianFields.WhiteNoise.Isonormal

/-!
# DOZZ.GFF.HaarDistributionPartial

Finite Haar-coordinate truncations of the G4 field are continuous linear functionals on tests.
Their evaluations converge in `L²` to the accepted G4 evaluations.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped InnerProductSpace Distributions ENNReal Topology

namespace DOZZ

/-- The Haar basis used by the scale-space white noise underlying the equator field. -/
noncomputable abbrev equatorHaarBasis :=
  GaussianFields.scalarWhiteNoiseHilbertBasis 3

/-- The `i`th Haar coordinate functional of the deterministic kernel map. -/
noncomputable def equatorHaarCoordinateCLM
    (i : GaussianFields.HaarBasisIndex 3) : Distr :=
  (innerSL ℝ (equatorHaarBasis i)).comp equatorKernelLimitMapCLM

variable (s : Finset (GaussianFields.HaarBasisIndex 3)) (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)

include s ω in
/-- The finite Haar expansion of the samplewise equator distribution. -/
noncomputable def equatorHaarPartialDistribution
     : Distr :=
  ∑ i ∈ s, (ω i) • equatorHaarCoordinateCLM i

@[simp]
theorem equatorHaarCoordinateCLM_apply
    (i : GaussianFields.HaarBasisIndex 3) (f : TestFn) :
    equatorHaarCoordinateCLM i f =
      ⟪equatorHaarBasis i, equatorKernelLimitMap f⟫_ℝ := by
  continuity

include s ω in
theorem equatorHaarPartialDistribution_apply
     (f : TestFn) :
    equatorHaarPartialDistribution s ω f =
      ∑ i ∈ s, ω i * ⟪equatorHaarBasis i, equatorKernelLimitMap f⟫_ℝ := by
  simp [equatorHaarPartialDistribution, equatorHaarCoordinateCLM_apply, smul_eq_mul]

include s ω in
/-- The finite sample evaluation is the corresponding concrete Gaussian-coordinate sum. -/
theorem equatorHaarPartialDistribution_apply_eq_gaussianLinearCombination
     (f : TestFn) :
    equatorHaarPartialDistribution s ω f =
      GaussianFields.gaussianLinearCombination s
        (fun i => equatorHaarBasis.repr (equatorKernelLimitMap f) i) ω := by
  rw [equatorHaarPartialDistribution_apply,
    GaussianFields.gaussianLinearCombination_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [equatorHaarBasis.repr_apply_apply]
  simp [GaussianFields.gaussianCoordinate, mul_comm]

/-- Every finite Haar partial evaluation is measurable on the product sample space. -/
theorem measurable_equatorHaarPartialDistribution_apply
    (s : Finset (GaussianFields.HaarBasisIndex 3)) (f : TestFn) :
    Measurable (fun ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2 =>
      equatorHaarPartialDistribution s ω f) := by
  have hfun : (fun ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2 =>
      equatorHaarPartialDistribution s ω f) =
      GaussianFields.gaussianLinearCombination s
        (fun i => equatorHaarBasis.repr (equatorKernelLimitMap f) i) := by
    funext ω
    exact equatorHaarPartialDistribution_apply_eq_gaussianLinearCombination s ω f
  measurability



/-- Haar partial sums of each fixed test converge in `L²` to the G4 evaluation. -/
theorem equatorHaarPartialEvaluation_tendsto_Lp (f : TestFn) :
    Tendsto
      (fun s : Finset (GaussianFields.HaarBasisIndex 3) =>
        GaussianFields.gaussianPartialSumLp s
          (equatorHaarBasis.repr (equatorKernelLimitMap f)))
      atTop (𝓝 (equatorFieldL2 f)) := GaussianFields.tendsto_gaussianPartialSumLp
    (equatorHaarBasis.repr (equatorKernelLimitMap f))

/-- The concrete Haar evaluations converge in measure to the G4 evaluation. This uniform
convergence-in-measure statement is the input for the countable common-subsequence extraction. -/
theorem equatorHaarPartialEvaluation_tendstoInMeasure (f : TestFn) :
    TendstoInMeasure
      (GaussianFields.gaussianSequenceMeasure (GaussianFields.HaarBasisIndex 3))
      (fun n ω => equatorHaarPartialDistribution
        (GaussianFields.gaussianIndexTruncation
          (GaussianFields.HaarBasisIndex 3) n) ω f) atTop
      (GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap f)) := by
  let μ := GaussianFields.gaussianSequenceMeasure
    (GaussianFields.HaarBasisIndex 3)
  let c := equatorHaarBasis.repr (equatorKernelLimitMap f)
  let F : ℕ → Lp ℝ 2 μ := fun n =>
    GaussianFields.gaussianPartialSumLp
      (GaussianFields.gaussianIndexTruncation
        (GaussianFields.HaarBasisIndex 3) n) c
  have hLp : Tendsto F atTop
      (𝓝 (GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap f))) := by
    change Tendsto
      (fun n => GaussianFields.gaussianPartialSumLp
        (GaussianFields.gaussianIndexTruncation
          (GaussianFields.HaarBasisIndex 3) n) c) atTop
      (𝓝 (equatorFieldL2 f))
    exact (equatorHaarPartialEvaluation_tendsto_Lp f).comp
      (GaussianFields.tendsto_gaussianIndexTruncation
        (GaussianFields.HaarBasisIndex 3))
  have hInMeasure  :=
    tendstoInMeasure_of_tendsto_Lp (p := (2 : ℝ≥0∞)) hLp
  have hpartial : ∀ n,
      (fun ω => equatorHaarPartialDistribution
        (GaussianFields.gaussianIndexTruncation
          (GaussianFields.HaarBasisIndex 3) n) ω f) =ᵐ[μ] ⇑(F n) := by
    intro n
    have hcoeff := GaussianFields.gaussianPartialSumLp_coeFn
      (GaussianFields.gaussianIndexTruncation
        (GaussianFields.HaarBasisIndex 3) n) c
    filter_upwards [hcoeff] with ω hω
    rw [equatorHaarPartialDistribution_apply_eq_gaussianLinearCombination]
    exact hω.symm
  exact hInMeasure.congr_left fun n => (hpartial n).symm


end DOZZ

end
