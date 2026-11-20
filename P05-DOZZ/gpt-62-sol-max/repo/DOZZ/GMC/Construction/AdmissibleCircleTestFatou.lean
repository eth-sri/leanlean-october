/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion
import DOZZ.GMC.Construction.CircleCutoffTestMass
import DOZZ.GMC.Construction.FatouInMeasure
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Expected test-mass bounds for admissible versions of circle cutoffs. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A nonnegative compact circle test against any admissible limit has expected mass at most its
reference mass. The proof uses cutoff intensity and Fatou along convergence in measure. -/
theorem admissibleCircleVersion_expected_test_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hf : ∀ x, 0 ≤ f x) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, f x ∂M ω) ∂P ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure := by
  let φ := fun x => ENNReal.ofReal (f x)
  let μ := fun r ω => regularizedGMC P Xc γ r ω
  let F := fun r ω => (∫⁻ x, φ x ∂μ r ω).toReal
  have hm : Measurable φ := ENNReal.measurable_ofReal.comp f.continuous.measurable
  have hmeas (r) : Measurable (F r) := ENNReal.measurable_toReal.comp
    ((Measure.measurable_lintegral hm).comp (regularizedGMC_measurable P X hX Xc hXc γ r))
  have hconv (r) : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ x, f x ∂μ r ω) = ∫⁻ x, φ x ∂μ r ω := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
    letI := hω
    exact ofReal_integral_eq_lintegral_ofReal (f.integrable _) (ae_of_all _ hf)
  have hT := TendstoInMeasure.congr (fun r => (hconv r).mono fun ω h => by
    change regularizedLogChaosTestMass P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f = F r ω
    rw [circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω f]
    exact (ENNReal.toReal_ofReal (integral_nonneg hf)).symm.trans (congrArg ENNReal.toReal h))
    (ae_of_all _ fun _ => rfl) (hM.2.2.2 f hfc (Set.subset_univ _))
  refine lintegral_ofReal_limit_le_of_tendstoInMeasure P F _ _ hmeas hT fun r => ?_
  exact (lintegral_mono fun ω => ENNReal.ofReal_toReal_le).trans
    (regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r φ hm).le

end DOZZ.Proofs
