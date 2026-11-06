/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneAffineSoftMaxBounds
public import DOZZ.GMC.FiniteChaosSmoothEndpoint
public import DOZZ.GMC.FiniteChaosMean

/-! Finite Kahane comparison for finite maxima of affine tests. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω κ : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : Fintype κ] [_inst3 : Nonempty κ] (P : Measure Ω) [_inst5 : IsFiniteMeasure P] (m : Ω → ℝ) (hm : Integrable m P) (a b : κ → ℝ)

include Ω κ _inst1 _inst2 _inst3 P _inst5 m hm a b in
/-- An affine maximum applied to an integrable mass is integrable. -/
theorem affineMax_comp_integrable
     : Integrable (fun ω => affineMax a b (m ω)) P := by
  obtain ⟨C, hC, hbound⟩ := affineMax_linear_growth a b
  apply ((hm.norm.add (integrable_const 1)).const_mul C).mono'
    ((affineMax_continuous a b).measurable.comp_aemeasurable hm.aemeasurable).aestronglyMeasurable
  exact ae_of_all _ fun ω => hbound (m ω)

include Ω κ _inst1 _inst2 _inst3 P _inst5 m hm a b in
/-- Smooth affine maxima converge in expectation for any integrable mass. -/
theorem affineSoftMax_integral_tendsto
     :
    Tendsto (fun n : ℕ => ∫ ω, affineSoftMax a b ((n : ℝ) + 1) (m ω) ∂P) atTop
      (𝓝 (∫ ω, affineMax a b (m ω) ∂P)) := by
  obtain ⟨C, hC, hbound⟩ := affineMax_linear_growth a b
  let L : ℝ := Real.log (Fintype.card κ : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  let bound : Ω → ℝ := fun ω => C * (‖m ω‖ + 1) + L
  have hboundInt  :=
    ((hm.norm.add (integrable_const 1)).const_mul C).add (integrable_const L)
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    have hcont : Continuous (affineSoftMax a b ((n : ℝ) + 1)) :=
      continuous_iff_continuousAt.mpr fun x =>
        (affineSoftMax_hasDerivAt a b _ x (by positivity)).continuousAt
    fun_prop (disch := positivity)
  · exact hboundInt
  · intro n
    filter_upwards [] with ω
    have h := affineSoftMax_bounds a b ((n : ℝ) + 1) (m ω) (by positivity)
    have herr : L / ((n : ℝ) + 1) ≤ L := by
      bound
    have habs : |affineSoftMax a b ((n : ℝ) + 1) (m ω)| ≤
        |affineMax a b (m ω)| + L := by
      grind
    have hlinear : |affineMax a b (m ω)| ≤ C * (‖m ω‖ + 1) := hbound (m ω)
    exact habs.trans (add_le_add hlinear le_rfl)
  · exact ae_of_all _ fun ω => affineSoftMax_tendsto a b (m ω)

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
  let  := hX.1
  let  := hY.1
  have hmX := (finiteChaosMass_integral PX X hX a γ).1
  have hmY := (finiteChaosMass_integral PY Y hY a γ).1
  have horder (n : ℕ) :
      (∫ ω, affineSoftMax c d ((n : ℝ) + 1) (DOZZ.finiteChaosMass PX X a γ ω) ∂PX) ≤
        ∫ ω, affineSoftMax c d ((n : ℝ) + 1) (DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
    have hβ : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨B₁, B₂, hB₁, hB₂, hnonneg⟩ := affineSoftMax_derivative_bounds c d _ hβ.le
    apply kahane_finite_smooth_convex PX PY X Y hX hY a ha γ
      (affineSoftMax c d _) (affineSoftMaxDeriv c d _) (affineSoftMaxSecondDeriv c d _)
      B₁ B₂ (fun x => affineSoftMax_hasDerivAt c d _ x hβ.ne')
      (fun x => affineSoftMaxDeriv_hasDerivAt c d _ x) _ hB₁ hB₂
      (fun x _ => hnonneg x) hcov
    change Measurable (fun x => affineSoftMaxSecondDeriv c d ((n : ℝ) + 1) x)
    unfold affineSoftMaxSecondDeriv affineSoftMaxSum
      affineSoftMaxSlopeSum affineSoftMaxSlopeSquareSum
    fun_prop
  exact le_of_tendsto_of_tendsto
    (affineSoftMax_integral_tendsto PX _ hmX c d)
    (affineSoftMax_integral_tendsto PY _ hmY c d) (Filter.Eventually.of_forall horder)


end DOZZ.Proofs
