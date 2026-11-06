/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.IsCircleAverage
import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
import DOZZ.GFFStructure.GaussianClosure

/-! Finite circle-average families are jointly Gaussian, by Gaussian closure of the field. -/


open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every finite family of circle averages of an equator GFF is centered jointly Gaussian. -/
theorem circleAverage_finite_family_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (p : ι → ℂ × ℝ) :
    IsCenteredJointlyGaussian P (fun ω i => Xc ω (p i).1 (p i).2) := by
  obtain ⟨hProcess, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  refine ⟨hX.1, ?_, ?_⟩
  · intro i
    exact hProcess.aemeasurable (p i)
  · intro a
    let S : Ω → ℝ := fun ω => ∑ i, a i * Xc ω (p i).1 (p i).2
    have hWeighted : IsGaussianProcess
        (fun i => fun ω => a i * Xc ω (p i).1 (p i).2) P := by
      have hParam : IsGaussianProcess
          (fun i => fun ω => Xc ω (p i).1 (p i).2) P := by
        simpa [Function.comp_def] using hProcess.comp_right p
      simpa [smul_eq_mul] using hParam.smul a
    have hLaw : HasGaussianLaw S P := by
      simpa [S, smul_eq_mul] using
        hWeighted.hasGaussianLaw_fun_sum (I := Finset.univ)
    have hMeanS : (∫ ω, S ω ∂P) = 0 := by
      dsimp [S]
      rw [integral_finsetSum]
      · simp [integral_const_mul, hMean, mul_zero, Finset.sum_const_zero]
      · intro i hi
        exact (hProcess.hasGaussianLaw_eval (p i)).integrable.const_mul (a i)
    refine ⟨hLaw.memLp_two, ?_⟩
    refine ⟨(Var[S; P]).toNNReal, ?_⟩
    simpa [hMeanS] using hLaw.map_eq_gaussianReal

end DOZZ.Proofs
