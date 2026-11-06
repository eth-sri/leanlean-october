/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneAffineSoftMaxBounds
public import DOZZ.GMC.FiniteChaosSmoothEndpoint
public import DOZZ.GMC.FiniteChaosMean

/-! Finite Kahane comparison for finite maxima of affine tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs
section
variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [Nonempty κ] (P : Measure Ω) [IsFiniteMeasure P] (m : Ω → ℝ)
section
variable (hm : Integrable m P) (a b : κ → ℝ)
include hm

/-- An affine maximum applied to an integrable mass is integrable. -/
theorem affineMax_comp_integrable
    : Integrable (fun ω => affineMax a b (m ω)) P := by
  obtain ⟨C, hC, hbound⟩ := affineMax_linear_growth a b
  apply ((hm.norm.add (integrable_const 1)).const_mul C).mono'
    ((affineMax_continuous a b).measurable.comp_aemeasurable hm.aemeasurable).aestronglyMeasurable
  simp_all

/-- Smooth affine maxima converge in expectation for any integrable mass. -/
theorem affineSoftMax_integral_tendsto
    :
    Tendsto (fun n : ℕ => ∫ ω, affineSoftMax a b ((n : ℝ) + 1) (m ω) ∂P) atTop
      (𝓝 (∫ ω, affineMax a b (m ω) ∂P)) := by
  obtain ⟨C, hC, hbound⟩ := affineMax_linear_growth a b
  let L := Real.log (Fintype.card κ : ℝ)
  have hL : 0 ≤ L := by positivity
  let bound : Ω → ℝ := fun ω => C * (‖m ω‖ + 1) + L
  have hboundInt : Integrable bound P :=
    by fun_prop
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    have hcont : Continuous (affineSoftMax a b ((n : ℝ) + 1)) :=
      continuous_iff_continuousAt.mpr fun x =>
        (affineSoftMax_hasDerivAt a b _ x (by positivity)).continuousAt
    fun_prop
  · exact hboundInt
  · intro n
    filter_upwards [] with ω
    have h := affineSoftMax_bounds a b ((n : ℝ) + 1) (m ω) (by positivity)
    have herr : L / ((n : ℝ) + 1) ≤ L := by
      bound
    have habs : |affineSoftMax a b ((n : ℝ) + 1) (m ω)| ≤
        |affineMax a b (m ω)| + L := by
      grind
    have hlinear : |affineMax a b (m ω)| ≤ C * (‖m ω‖ + 1) := by
      simp_all
    exact habs.trans (add_le_add hlinear le_rfl)
  · exact ae_of_all _ fun ω => affineSoftMax_tendsto a b (m ω)

end

end

/-- Finite maxima of affine functions have the covariance-ordered Kahane expectation inequality. -/
theorem kahane_finite_affine_max
    {ΩX ΩY ι κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [Fintype κ] [Nonempty κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ) (c d : κ → ℝ)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    (∫ ω, affineMax c d (DOZZ.finiteChaosMass PX X a γ ω) ∂PX) ≤
      ∫ ω, affineMax c d (DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  have horder (n : ℕ) :
      (∫ ω, affineSoftMax c d (n + 1) (DOZZ.finiteChaosMass PX X a γ ω) ∂PX) ≤
        ∫ ω, affineSoftMax c d (n + 1) (DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
    have hβ : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨B₁, B₂, hB₁, hB₂, hnonneg⟩ := affineSoftMax_derivative_bounds c d _ hβ.le
    apply kahane_finite_smooth_convex PX PY X Y hX hY a ha γ
      (affineSoftMax c d _) _ _
      B₁ B₂ (fun x => affineSoftMax_hasDerivAt c d _ x hβ.ne')
      (affineSoftMaxDeriv_hasDerivAt c d _) _ hB₁ hB₂
      (fun x _ => hnonneg x) hcov
    unfold affineSoftMaxSecondDeriv affineSoftMaxSum
      affineSoftMaxSlopeSum affineSoftMaxSlopeSquareSum
    fun_prop
  exact le_of_tendsto_of_tendsto
    (affineSoftMax_integral_tendsto PX _ ((finiteChaosMass_integral PX X hX a γ).1) c d)
    (affineSoftMax_integral_tendsto PY _ ((finiteChaosMass_integral PY Y hY a γ).1) c d) (Filter.Eventually.of_forall horder)


end DOZZ.Proofs
