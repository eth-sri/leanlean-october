/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosSmoothKahaneComparison
public import DOZZ.GMC.FiniteChaosTestGrowth
public import DOZZ.GMC.FiniteGaussianExponentialIntegrability

/-! Gaussian-growth integrability for the smooth Kahane interpolation derivative. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

private theorem kahaneSumVectorField_abs_sum_le
    {ι : Type*} [Fintype ι]
    t (ht : 0 < t) (ht1 : t < 1) (z : Sum ι ι → ℝ) :
    (∑ i, |kahaneSumVectorField t z i|) ≤ ∑ k, |z k| := by
  classical
  have hsqrtT : Real.sqrt t ≤ 1 := by
    have := Real.sq_sqrt (le_of_lt ht)
    nlinarith [sq_nonneg (Real.sqrt t - 1)]
  have hsqrtOne : Real.sqrt (1 - t) ≤ 1 := by
    have := Real.sq_sqrt (le_of_lt (show 0 < 1 - t by linarith))
    nlinarith [sq_nonneg (Real.sqrt (1 - t) - 1)]
  calc
    _ ≤ ∑ i, (|z (Sum.inl i)| + |z (Sum.inr i)|) := by
      apply Finset.sum_le_sum
      intro i hi
      dsimp [kahaneSumVectorField]
      calc
        |Real.sqrt t * z (Sum.inl i) + Real.sqrt (1 - t) * z (Sum.inr i)| ≤
            |Real.sqrt t * z (Sum.inl i)| +
              |Real.sqrt (1 - t) * z (Sum.inr i)| := abs_add_le _ _
        _ = Real.sqrt t * |z (Sum.inl i)| +
              Real.sqrt (1 - t) * |z (Sum.inr i)| := by
                rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
                  abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ |z (Sum.inl i)| + |z (Sum.inr i)| := by
              apply add_le_add
              · calc
                  Real.sqrt t * |z (Sum.inl i)| ≤ 1 * |z (Sum.inl i)| :=
                    mul_le_mul_of_nonneg_right hsqrtT (abs_nonneg _)
                  _ = |z (Sum.inl i)| := one_mul _
              · calc
                  Real.sqrt (1 - t) * |z (Sum.inr i)| ≤ 1 * |z (Sum.inr i)| :=
                    mul_le_mul_of_nonneg_right hsqrtOne (abs_nonneg _)
                  _ = |z (Sum.inr i)| := one_mul _
    _ = ∑ i, |z (Sum.inl i)| + ∑ i, |z (Sum.inr i)| := by
      rw [Finset.sum_add_distrib]
    _ = ∑ k, |z k| := by rw [Fintype.sum_sum_type]

set_option linter.style.haveILetI false in


/-- Dominated differentiation and the Gaussian-IBP calculation together show that a smooth
convex test has nonpositive derivative along an interior finite Kahane interpolation time.
The local domination hypotheses are exactly those consumed by the parametric integral theorem. -/
theorem kahaneSmoothInterpolationExpectation_hasDerivAt_nonpos
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    X Y
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a vX vY : ι → ℝ) (ha : ∀ i, 0 ≤ a i) γ t ε
    (F F' F'' : ℝ → ℝ) B₁ B₂
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF'bound : ∀ x, ‖F' x‖ ≤ B₁)
    (hF''bound : ∀ x, ‖F'' x‖ ≤ B₂)
    (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x)
    (hε : 0 < ε) (hεleft : ε ≤ t) (hεright : ε ≤ 1 - t)
    (hMeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun ω : ΩX × ΩY => F (kahaneInterpolatedMass X Y vX vY a γ s ω)) (PX.prod PY))
    (hInt : Integrable
      (fun ω : ΩX × ΩY => F (kahaneInterpolatedMass X Y vX vY a γ t ω)) (PX.prod PY))
    (hDMeas : AEStronglyMeasurable
      (fun ω : ΩX × ΩY => kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω)
      (PX.prod PY))
    (b : ΩX × ΩY → ℝ) (hb : Integrable b (PX.prod PY))
    (hbound : ∀ᵐ ω ∂(PX.prod PY), ∀ s ∈ Metric.ball t ε,
      ‖kahaneInterpolatedTestDerivative X Y vX vY a γ F' s ω‖ ≤ b ω)
    (hvX : ∀ i, vX i = DOZZ.gaussianCovariance PX
      (fun ω => X ω i) (fun ω => X ω i))
    (hvY : ∀ i, vY i = DOZZ.gaussianCovariance PY
      (fun ω => Y ω i) (fun ω => Y ω i))
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX
      (fun ω => X ω i) (fun ω => X ω j) ≤ DOZZ.gaussianCovariance PY
      (fun ω => Y ω i) (fun ω => Y ω j)) :
    HasDerivAt
      (fun s => ∫ ω : ΩX × ΩY,
        F (kahaneInterpolatedMass X Y vX vY a γ s ω) ∂(PX.prod PY))
      (∫ ω : ΩX × ΩY,
        kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY)) t ∧
    (∫ ω : ΩX × ΩY,
      kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY)) ≤ 0 := by
  have kahaneSmoothInterpolation_integrand_nonpos_of_bounded_derivatives (PX : Measure ΩX) (PY : Measure ΩY) X Y (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y) (a : ι → ℝ) (vX : ι → ℝ) (vY : ι → ℝ) (ha : ∀ i, 0 ≤ a i) γ t F' F'' B₁ B₂ (hF'meas : Measurable F') (hF''meas : Measurable F'') (hF' : ∀ x, HasDerivAt F' (F'' x) x) (hF'bound : ∀ x, ‖F' x‖ ≤ B₁) (hF''bound : ∀ x, ‖F'' x‖ ≤ B₂) (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x) (ht : 0 < t) (ht1 : t < 1) (hvX : ∀ i, vX i = DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i)) (hvY : ∀ i, vY i = DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i)) (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤ DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) : ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY) ≤ 0 := by
    classical
    have hB₁ : 0 ≤ B₁ := by
      by_contra h
      have hneg : B₁ < 0 := lt_of_not_ge h
      have hbound := hF'bound 0
      have hnonneg := norm_nonneg (F' 0)
      linarith
    have hB₂ : 0 ≤ B₂ := by
      by_contra h
      have hneg : B₂ < 0 := lt_of_not_ge h
      have hbound := hF''bound 0
      have hnonneg := norm_nonneg (F'' 0)
      linarith
    letI : IsProbabilityMeasure PX := hX.1
    letI : IsProbabilityMeasure PY := hY.1
    let μ : Measure (ΩX × ΩY) := PX.prod PY
    let v : ι → ℝ := fun i => t * vX i + (1 - t) * vY i
    let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
      | Sum.inl i => X ω.1 i
      | Sum.inr i => Y ω.2 i
    have hZ : IsCenteredJointlyGaussian μ Z :=
      independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
    let c : Sum ι ι → ℝ := fun _ => 2 * |γ|
    have hEnv : Integrable (fun ω => Real.exp (∑ k, c k * |Z ω k|)) μ := by
      exact centeredJointlyGaussian_abs_linear_exp_integrable μ Z hZ c
    have hCoordEnv k : Integrable
        (fun ω => Z ω k * Real.exp (∑ j, c j * |Z ω j|)) μ :=
      centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable μ Z hZ c k
    let score : ΩX × ΩY → ι → ℝ := fun ω i =>
      kahaneSumVectorScore a v γ t F' (Z ω) i
    let fieldD : ΩX × ΩY → ι → ι → ℝ := fun ω i j =>
      kahaneSumVectorFieldScoreDerivative a v γ t F' F'' (Z ω) i j
    let K : ΩX × ΩY → ι → ι → ℝ := fun ω i j =>
      finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i *
        finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j *
        F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)))
    obtain ⟨M, hM, hscoreBound⟩ :=
      finiteChaosVectorTestScore_exp_growth_bounds a v γ B₁ B₂ hB₁ hB₂
        F' F'' hF'bound hF''bound
    have hsum_le (z : Sum ι ι → ℝ) :
        2 * (|γ| * ∑ i, |kahaneSumVectorField t z i|) ≤
          ∑ k, c k * |z k| := by
      have hfield : ∑ i, |kahaneSumVectorField t z i| ≤
          ∑ i, |z (Sum.inl i)| + ∑ i, |z (Sum.inr i)| := by
        calc
          _ ≤ ∑ k, |z k| := kahaneSumVectorField_abs_sum_le t ht ht1 z
          _ = _ := by rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_sum_type, c]
      calc
        2 * (|γ| * ∑ i, |kahaneSumVectorField t z i|) ≤
            2 * (|γ| * (∑ i, |z (Sum.inl i)| + ∑ i, |z (Sum.inr i)|)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hfield (abs_nonneg γ)) (by norm_num)
        _ = 2 * |γ| * (∑ i, |z (Sum.inl i)| + ∑ i, |z (Sum.inr i)|) := by
          ring
        _ = ∑ i, 2 * |γ| * |z (Sum.inl i)| +
            ∑ i, 2 * |γ| * |z (Sum.inr i)| := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
    have hscoreBound' (z : Sum ι ι → ℝ) i :
        ‖kahaneSumVectorScore a v γ t F' z i‖ ≤
          M * Real.exp (∑ k, c k * |z k|) := by
      have h := (hscoreBound (kahaneSumVectorField t z) i i).1
      calc
        _ ≤ M * Real.exp (2 * (|γ| * ∑ j, |kahaneSumVectorField t z j|)) :=
          (hscoreBound (kahaneSumVectorField t z) i i).1
        _ ≤ M * Real.exp (∑ k, c k * |z k|) := by
          apply mul_le_mul_of_nonneg_left _ hM
          exact Real.exp_le_exp.mpr (hsum_le z)
    have hderivBound' (z : Sum ι ι → ℝ) i k :
        ‖kahaneSumVectorScoreDerivative a v γ t F' F'' z i k‖ ≤
          M * Real.exp (∑ j, c j * |z j|) := by
      cases k with
      | inl j =>
          have hsqrt : Real.sqrt t ≤ 1 := by
            have hs := Real.sq_sqrt (le_of_lt ht)
            nlinarith [sq_nonneg (Real.sqrt t - 1)]
          calc
            ‖Real.sqrt t * kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j‖ =
                Real.sqrt t * ‖kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j‖ := by
                  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            _ ≤ Real.sqrt t * (M * Real.exp
                (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|))) :=
                  mul_le_mul_of_nonneg_left
                    (hscoreBound (kahaneSumVectorField t z) i j).2 (Real.sqrt_nonneg _)
            _ ≤ M * Real.exp (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|)) := by
                  calc
                    _ ≤ 1 * (M * Real.exp
                        (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|))) :=
                      mul_le_mul_of_nonneg_right hsqrt (by positivity)
                    _ = _ := one_mul _
            _ ≤ M * Real.exp (∑ l, c l * |z l|) := by
                  apply mul_le_mul_of_nonneg_left _ hM
                  exact Real.exp_le_exp.mpr (hsum_le z)
      | inr j =>
          have hsqrt : Real.sqrt (1 - t) ≤ 1 := by
            have hs := Real.sq_sqrt (le_of_lt (by linarith : 0 < 1 - t))
            nlinarith [sq_nonneg (Real.sqrt (1 - t) - 1)]
          calc
            ‖Real.sqrt (1 - t) * kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j‖ =
                Real.sqrt (1 - t) *
                  ‖kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j‖ := by
                    rw [norm_mul, Real.norm_eq_abs,
                      abs_of_nonneg (Real.sqrt_nonneg _)]
            _ ≤ Real.sqrt (1 - t) * (M * Real.exp
                (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|))) :=
                  mul_le_mul_of_nonneg_left
                    (hscoreBound (kahaneSumVectorField t z) i j).2
                    (Real.sqrt_nonneg _)
            _ ≤ M * Real.exp (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|)) := by
                  calc
                    _ ≤ 1 * (M * Real.exp
                        (2 * (|γ| * ∑ l, |kahaneSumVectorField t z l|))) :=
                      mul_le_mul_of_nonneg_right hsqrt (by positivity)
                    _ = _ := one_mul _
            _ ≤ M * Real.exp (∑ l, c l * |z l|) := by
                  apply mul_le_mul_of_nonneg_left _ hM
                  exact Real.exp_le_exp.mpr (hsum_le z)
    have hZae : AEMeasurable (fun ω => Z ω) μ := by
      apply AEMeasurable.of_eval
      intro k
      cases k with
      | inl i =>
          exact (show AEMeasurable (fun ω => X ω i) (μ.map Prod.fst) by rw [measurePreserving_fst.map_eq]; exact hX.2.1 i).comp_measurable measurable_fst
      | inr i =>
          exact (show AEMeasurable (fun ω => Y ω i) (μ.map Prod.snd) by rw [measurePreserving_snd.map_eq]; exact hY.2.1 i).comp_measurable measurable_snd
    have hScoreMeas : ∀ i, Measurable (fun z => kahaneSumVectorScore a v γ t F' z i) := by
      intro i
      dsimp [kahaneSumVectorScore, finiteChaosVectorTestScore]
      fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
    have hScoreAEMeas : ∀ i, AEStronglyMeasurable (fun ω => score ω i) μ := by
      intro i
      exact (hScoreMeas i).aestronglyMeasurable.comp_aemeasurable hZae
    have hXae i : AEMeasurable (fun ω : ΩX × ΩY => X ω.1 i) μ := by
      exact (show AEMeasurable (fun ω => X ω i) (μ.map Prod.fst) by rw [measurePreserving_fst.map_eq]; exact hX.2.1 i).comp_measurable measurable_fst
    have hYae i : AEMeasurable (fun ω : ΩX × ΩY => Y ω.2 i) μ := by
      exact (show AEMeasurable (fun ω => Y ω i) (μ.map Prod.snd) by rw [measurePreserving_snd.map_eq]; exact hY.2.1 i).comp_measurable measurable_snd
    have hScoreInt : ∀ i, Integrable (fun ω => score ω i) μ := by
      intro i
      apply hEnv.const_mul M |>.mono'
      · exact hScoreAEMeas i
      · filter_upwards [] with ω
        simpa [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hM (Real.exp_nonneg _))] using hscoreBound' (Z ω) i
    have hXScoreInt : ∀ i, Integrable
        (fun ω : ΩX × ΩY => X ω.1 i * score ω i) μ := by
      intro i
      have hMajor : Integrable (fun ω => M * |Z ω (Sum.inl i)| *
          Real.exp (∑ k, c k * |Z ω k|)) μ := by
        convert ((hCoordEnv (Sum.inl i)).norm).const_mul M using 1
        ext ω
        simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        ring
      apply hMajor.mono' (by exact (hXae i).aestronglyMeasurable.mul (hScoreAEMeas i))
      filter_upwards [] with ω
      change ‖X ω.1 i * score ω i‖ ≤
        M * |Z ω (Sum.inl i)| * Real.exp (∑ k, c k * |Z ω k|)
      calc
        ‖X ω.1 i * score ω i‖ = |X ω.1 i| * ‖score ω i‖ := by
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ |X ω.1 i| * (M * Real.exp (∑ k, c k * |Z ω k|)) :=
          mul_le_mul_of_nonneg_left (hscoreBound' (Z ω) i) (abs_nonneg _)
        _ = M * |X ω.1 i| * Real.exp (∑ k, c k * |Z ω k|) := by ring
    have hYScoreInt : ∀ i, Integrable
        (fun ω : ΩX × ΩY => Y ω.2 i * score ω i) μ := by
      intro i
      have hMajor : Integrable (fun ω => M * |Z ω (Sum.inr i)| *
          Real.exp (∑ k, c k * |Z ω k|)) μ := by
        convert ((hCoordEnv (Sum.inr i)).norm).const_mul M using 1
        ext ω
        simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        ring
      apply hMajor.mono' (by exact (hYae i).aestronglyMeasurable.mul (hScoreAEMeas i))
      filter_upwards [] with ω
      change ‖Y ω.2 i * score ω i‖ ≤
        M * |Z ω (Sum.inr i)| * Real.exp (∑ k, c k * |Z ω k|)
      calc
        ‖Y ω.2 i * score ω i‖ = |Y ω.2 i| * ‖score ω i‖ := by
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ |Y ω.2 i| * (M * Real.exp (∑ k, c k * |Z ω k|)) :=
          mul_le_mul_of_nonneg_left (hscoreBound' (Z ω) i) (abs_nonneg _)
        _ = M * |Y ω.2 i| * Real.exp (∑ k, c k * |Z ω k|) := by ring
    have hFieldDMeas : ∀ i j, Measurable
        (fun z => kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j) := by
      intro i j
      by_cases hij : i = j
      · simp [kahaneSumVectorFieldScoreDerivative,
          finiteChaosVectorTestScoreDerivative, hij]
        fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
      · simp [kahaneSumVectorFieldScoreDerivative,
          finiteChaosVectorTestScoreDerivative, hij]
        fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
    have hFieldDInt : ∀ i j, Integrable (fun ω => fieldD ω i j) μ := by
      intro i j
      apply hEnv.const_mul M |>.mono'
      · exact (show ∀ i j, AEStronglyMeasurable (fun ω => fieldD ω i j) μ by intro i j; exact (hFieldDMeas i j).aestronglyMeasurable.comp_aemeasurable hZae) i j
      · filter_upwards [] with ω
        calc
          ‖fieldD ω i j‖ ≤ M * Real.exp
              (2 * (|γ| * ∑ k, |kahaneSumVectorField t (Z ω) k|)) := by
            simpa [fieldD, kahaneSumVectorFieldScoreDerivative] using ((hscoreBound (kahaneSumVectorField t (Z ω)) i j).2)
          _ ≤ M * Real.exp (∑ k, c k * |Z ω k|) := by
            apply mul_le_mul_of_nonneg_left _ hM
            exact Real.exp_le_exp.mpr (hsum_le (Z ω))
    obtain ⟨W, hW, hWeightBound⟩ :=
      finiteChaosVectorWeight_absExp_bound a v γ
    let c2 : Sum ι ι → ℝ := fun _ => 2 * |γ|
    have hKInt : ∀ i j, Integrable (fun ω => K ω i j) μ := by
      intro i j
      have hpoint z :
          ‖finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) i *
            finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) j *
            F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t z))‖ ≤
          W ^ 2 * B₂ * Real.exp (∑ k, c2 k * |z k|) := by
        have hexp : 2 * (|γ| * ∑ k, |z k|) = ∑ k, c2 k * |z k| := by
          simp only [Fintype.sum_sum_type, c2]
          calc
            _ = 2 * |γ| * (∑ i, |z (Sum.inl i)| + ∑ i, |z (Sum.inr i)|) := by ring
            _ = _ := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              ring
        have hproduct :
            ‖finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) i‖ *
                ‖finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) j‖ *
                ‖F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t z))‖ ≤
              (W * Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|)) *
                (W * Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|)) * B₂ := by
          apply mul_le_mul
          · exact mul_le_mul (hWeightBound (kahaneSumVectorField t z) i) (hWeightBound (kahaneSumVectorField t z) j) (norm_nonneg _) (by positivity)
          · exact hF''bound _
          · positivity
          · positivity
        calc
          _ ≤ (W * Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|)) ^ 2 * B₂ := by
            rw [norm_mul, norm_mul]
            calc
              _ ≤ (W * Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|)) *
                    (W * Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|)) * B₂ :=
                hproduct
              _ = _ := by rw [pow_two]
          _ ≤ W ^ 2 * B₂ *
              Real.exp (2 * (|γ| * ∑ k, |kahaneSumVectorField t z k|)) := by
            have hExpSq x : Real.exp x ^ 2 = Real.exp (2 * x) := by
              calc
                _ = Real.exp x * Real.exp x := by rw [pow_two]
                _ = Real.exp (x + x) := by rw [← Real.exp_add]
                _ = Real.exp (2 * x) := by congr 1; ring
            calc
              _ = W ^ 2 * B₂ *
                  Real.exp (|γ| * ∑ k, |kahaneSumVectorField t z k|) ^ 2 := by ring
              _ = _ := by rw [hExpSq]
              _ ≤ _ := le_rfl
          _ ≤ W ^ 2 * B₂ * Real.exp (∑ k, c2 k * |z k|) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr ((show 2 * (|γ| * ∑ k, |kahaneSumVectorField t z k|) ≤ 2 * (|γ| * ∑ k, |z k|) by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (kahaneSumVectorField_abs_sum_le t ht ht1 z) (abs_nonneg γ)) (by norm_num)).trans_eq hexp)
      apply (centeredJointlyGaussian_abs_linear_exp_integrable μ Z hZ c2).const_mul (W ^ 2 * B₂) |>.mono'
      · exact (show ∀ i j, AEStronglyMeasurable (fun ω => K ω i j) μ by intro i j; exact ((show ∀ i j, Measurable (fun z => finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) i * finiteChaosVectorWeight a v γ (kahaneSumVectorField t z) j * F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t z))) by intro i j; fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]) i j).aestronglyMeasurable.comp_aemeasurable hZae) i j
      · filter_upwards [] with ω
        simpa [K, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg W) hB₂)
            (Real.exp_nonneg _))] using hpoint (Z ω)
    exact kahaneSmoothInterpolation_integrand_nonpos_of_gaussian_ibp
      PX PY X Y hX hY a vX vY ha γ t F' F'' hF'meas hF''meas hF' hF''nonneg
      ht ht1 hvX hvY hcov c (fun _ => by positivity) M hM hscoreBound' hderivBound' hScoreInt hXScoreInt hYScoreInt
      hFieldDInt hKInt
  constructor
  · exact kahaneInterpolatedExpectation_hasDerivAt PX PY X Y vX vY a γ t ε F F' hF
      hε hεleft hεright hMeas hInt hDMeas b hb hbound
  · have ht : 0 < t := lt_of_lt_of_le hε hεleft
    exact kahaneSmoothInterpolation_integrand_nonpos_of_bounded_derivatives
      PX PY X Y hX hY a vX vY ha γ t F' F'' B₁ B₂ hF'meas hF''meas hF'
      hF'bound hF''bound hF''nonneg ht (by linarith) hvX hvY hcov


end DOZZ.Proofs
