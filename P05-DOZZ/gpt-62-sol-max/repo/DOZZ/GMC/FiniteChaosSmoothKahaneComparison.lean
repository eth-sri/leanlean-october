/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestGrowth
public import DOZZ.GMC.FiniteChaosSmoothKahane
public import DOZZ.GMC.FiniteChaosInterpolationExpectation
public import DOZZ.GMC.FiniteGaussianInterpolationIdentity
public import DOZZ.GMC.FiniteGaussianProduct
public import DOZZ.GMC.FiniteGaussianIntegrationByPartsGrowth
public import DOZZ.GMC.FiniteGaussianTilt

/-! Smooth-test Kahane interpolation for finite Gaussian chaos sums. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

section
variable {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι] (PX : Measure ΩX)
  (PY : Measure ΩY)
include ΩX ΩY

/-- Covariance of two coordinates pulled back from the first factor of a product measure. -/
theorem gaussianCovariance_product_fst (X : ΩX → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hPY : IsProbabilityMeasure PY)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => X ω.1 i) (fun ω => X ω.1 j) =
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) := by
  let := hPY
  let := hX.1
  have hp : MeasurePreserving Prod.fst (PX.prod PY) PX := measurePreserving_fst
  have hmeas := (hX.2.1 i).mul (hX.2.1 j)
  have ha : AEStronglyMeasurable (fun ω => X ω i * X ω j) ((PX.prod PY).map Prod.fst) :=
    hp.map_eq.symm ▸ hmeas.aestronglyMeasurable
  simpa only [hp.map_eq, DOZZ.gaussianCovariance, Function.comp_def] using
    (integral_map hp.aemeasurable ha).symm

/-- Covariance of two coordinates pulled back from the second factor of a product measure. -/
theorem gaussianCovariance_product_snd (Y : ΩY → ι → ℝ)
    (hPX : IsProbabilityMeasure PX) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => Y ω.2 i) (fun ω => Y ω.2 j) =
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) := by
  let := hPX
  let := hY.1
  have hp : MeasurePreserving Prod.snd (PX.prod PY) PY := measurePreserving_snd
  have hmeas := (hY.2.1 i).mul (hY.2.1 j)
  have ha : AEStronglyMeasurable (fun ω => Y ω i * Y ω j) ((PX.prod PY).map Prod.snd) :=
    hp.map_eq.symm ▸ hmeas.aestronglyMeasurable
  simpa only [hp.map_eq, DOZZ.gaussianCovariance, Function.comp_def] using
    (integral_map hp.aemeasurable ha).symm

end

section
variable {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι] [DecidableEq ι]
  (PX : Measure ΩX) (PY : Measure ΩY) (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
  (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
include ΩX ΩY hX hY

/-- Cross covariance of independent coordinates on a product space is zero for centered
Gaussian families. -/
theorem gaussianCovariance_product_cross_eq_zero
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => X ω.1 i) (fun ω => Y ω.2 j) = 0 := by
  let  := hX.1
  let  := hY.1
  rw [DOZZ.gaussianCovariance]
  have hprod : (∫ ω : ΩX × ΩY, X ω.1 i * Y ω.2 j ∂PX.prod PY) =
      (∫ x, X x i ∂PX) * ∫ y, Y y j ∂PY := integral_prod_mul (fun x => X x i) (fun y => Y y j)
  rw [hprod, coord_mean PX X hX i, coord_mean PY Y hY j]
  simp

/-- The covariance of the concatenation of independent centered Gaussian vectors on a product
space is block diagonal. -/
theorem gaussianCovariance_product_concat
    (i j : Sum ι ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => match i with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k)
        (fun ω => match j with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k) =
      match i, j with
      | Sum.inl k, Sum.inl l =>
          DOZZ.gaussianCovariance PX (fun ω => X ω k) (fun ω => X ω l)
      | Sum.inr k, Sum.inr l =>
          DOZZ.gaussianCovariance PY (fun ω => Y ω k) (fun ω => Y ω l)
      | _, _ => 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          exact gaussianCovariance_product_fst PX PY X hX hY.1 i j
      | inr j =>
          apply gaussianCovariance_product_cross_eq_zero <;> assumption
  | inr i =>
      cases j with
      | inl j =>
          simpa [DOZZ.gaussianCovariance, mul_comm] using
          (gaussianCovariance_product_cross_eq_zero PX PY X Y hX hY j i)
      | inr j =>
          exact gaussianCovariance_product_snd PX PY Y hX.1 hY i j

end

private theorem kahaneSumVectorField_abs_sum_le
    {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (z : Sum ι ι → ℝ) :
    (∑ i, |kahaneSumVectorField t z i|) ≤ ∑ k, |z k| := by
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.mpr ht1.le))
    (mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.mpr (by linarith)))

/-- Gaussian integration by parts cancels the Wick normalization against the diagonal
of the Hessian. The remaining terms have the sign of the entrywise covariance difference. -/
theorem kahaneSmoothInterpolation_integrand_nonpos_of_bounded_derivatives
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a vX vY : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ t : ℝ)
    (F' F'' : ℝ → ℝ) (B₁ B₂ : ℝ)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF'bound : ∀ x, 0 ≤ x → ‖F' x‖ ≤ B₁)
    (hF''bound : ∀ x, 0 ≤ x → ‖F'' x‖ ≤ B₂)
    (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x)
    (ht : 0 < t) (ht1 : t < 1)
    (hvX : ∀ i, vX i = DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i))
    (hvY : ∀ i, vY i = DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i))
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY) ≤ 0 := by
  classical
  let μ := PX.prod PY
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
    | .inl i => X ω.1 i
    | .inr i => Y ω.2 i
  have hZ : IsCenteredJointlyGaussian μ Z :=
    independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
  have hZm : AEMeasurable Z μ := aemeasurable_pi_iff.mpr hZ.2.1
  let v := fun i => t * vX i + (1 - t) * vY i
  let S := kahaneSumVectorScore a v γ t F'
  let D := kahaneSumVectorFieldScoreDerivative a v γ t F' F''
  let D' := kahaneSumVectorScoreDerivative a v γ t F' F''
  let K := fun z i j => finiteChaosVectorPairScore a v γ F'' (kahaneSumVectorField t z) i j
  let c : Sum ι ι → ℝ := fun _ => 2 * |γ|
  let E := fun z : Sum ι ι → ℝ => Real.exp (∑ k, c k * |z k|)
  obtain ⟨M, hM, hbound⟩ := finiteChaosVectorTestScore_exp_growth_bounds a v ha γ B₁ B₂
    ((norm_nonneg _).trans (hF'bound 0 le_rfl)) ((norm_nonneg _).trans (hF''bound 0 le_rfl))
    F' F'' hF'bound hF''bound
  have hEnv (z : Sum ι ι → ℝ) : M * Real.exp (2 * (|γ| * ∑ i, |kahaneSumVectorField t z i|)) ≤ M * E z := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
    rw [show (∑ k, c k * |z k|) = (2 * |γ|) * ∑ k, |z k| by simp only [Finset.mul_sum, c], mul_assoc]
    gcongr
    exact kahaneSumVectorField_abs_sum_le t ht ht1 z
  have hS (z i) : ‖S z i‖ ≤ M * E z := (hbound _ i i).1.trans (hEnv z)
  have hD (z i j) : ‖D z i j‖ ≤ M * E z := (hbound _ i j).2.1.trans (hEnv z)
  have hK (z i j) : ‖K z i j‖ ≤ M * E z := (hbound _ i j).2.2.trans (hEnv z)
  have hD' (z i k) : ‖D' z i k‖ ≤ M * E z := by
    have hscale (s : ℝ) (hs : s ≤ 1) (j : ι) : ‖Real.sqrt s * D z i j‖ ≤ M * E z := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr hs)).trans (hD z i j)
    cases k with
    | inl j => exact hscale t ht1.le j
    | inr j => exact hscale (1 - t) (by linarith) j
  have hSm (i : ι) : Measurable (S · i) := by
    dsimp [S, kahaneSumVectorScore, finiteChaosVectorTestScore]
    fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hKm (i j : ι) : Measurable (K · i j) := by
    dsimp [K, finiteChaosVectorPairScore]
    fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hDm (i j : ι) : Measurable (D · i j) := by
    by_cases h : i = j <;> simp only [D, kahaneSumVectorFieldScoreDerivative,
      finiteChaosVectorTestScoreDerivative, h, ite_true, ite_false] <;>
      fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hD'm (i : ι) (k : Sum ι ι) : Measurable (D' · i k) := by
    cases k with
    | inl j => exact (hDm i j).const_mul _
    | inr j => exact (hDm i j).const_mul _
  have hInt {f : (Sum ι ι → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ z, ‖f z‖ ≤ M * E z) :
      Integrable (fun ω => f (Z ω)) μ := by
    exact ((centeredJointlyGaussian_abs_linear_exp_integrable μ Z hZ c).const_mul M).mono'
      (hf.comp_aemeasurable hZm).aestronglyMeasurable (ae_of_all _ fun ω => hb (Z ω))
  have hZS (i : ι) (k : Sum ι ι) : Integrable (fun ω => Z ω k * S (Z ω) i) μ := by
    apply ((centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable μ Z hZ c k).norm.const_mul M).mono'
    · exact (hZ.2.1 k).aestronglyMeasurable.mul ((hSm i).comp_aemeasurable hZm).aestronglyMeasurable
    · filter_upwards [] with ω
      change ‖Z ω k * S (Z ω) i‖ ≤ M * ‖Z ω k * E (Z ω)‖
      simp only [norm_mul, show ‖E (Z ω)‖ = E (Z ω) from abs_of_pos (Real.exp_pos _)]
      rw [mul_left_comm]
      gcongr
      exact hS (Z ω) i
  let covX := fun i j => gaussianCovariance PX (X · i) (X · j)
  let covY := fun i j => gaussianCovariance PY (Y · i) (Y · j)
  have hCov (k l : Sum ι ι) : gaussianCovariance μ (Z · k) (Z · l) =
      match k, l with
      | .inl i, .inl j => covX i j
      | .inr i, .inr j => covY i j
      | _, _ => 0 := gaussianCovariance_product_concat PX PY X Y hX hY k l
  let J := fun i j => ∫ ω, D (Z ω) i j ∂μ
  have hibp (i : ι) (k : Sum ι ι) : (∫ ω, Z ω k * S (Z ω) i ∂μ) =
      match k with
      | .inl j => Real.sqrt t * ∑ l, covX j l * J i l
      | .inr j => Real.sqrt (1 - t) * ∑ l, covY j l * J i l := by
    rw [finite_gaussian_integration_by_parts_of_absExp_bound μ Z hZ k (S · i) (D' · i)
      (hSm i) (hD'm i) c (fun _ => by dsimp [c]; positivity) M hM (hS · i) (hD' · i)
      (fun x d r => kahaneSumVectorScore_directional_hasDerivAt a v γ t F' F'' hF' x d i r),
      Fintype.sum_sum_type]
    cases k <;> simp only [hCov, D', kahaneSumVectorScoreDerivative, integral_const_mul, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add, Finset.mul_sum, J] <;>
      exact Finset.sum_congr rfl fun j _ => by ring
  let Kbar := fun i j => ∫ ω, K (Z ω) i j ∂μ
  let Sbar := fun i => ∫ ω, S (Z ω) i ∂μ
  have hessian (i j : ι) : γ * J i j = γ ^ 2 * Kbar i j + (if i = j then γ ^ 2 * Sbar i else 0) := by
    have h (z : Sum ι ι → ℝ) : γ * D z i j =
        γ ^ 2 * K z i j + (if i = j then γ ^ 2 * S z i else 0) := by
      by_cases he : i = j <;> simp only [D, K, S, kahaneSumVectorFieldScoreDerivative,
        finiteChaosVectorTestScoreDerivative, kahaneSumVectorScore, finiteChaosVectorTestScore,
        finiteChaosVectorPairScore, he, ite_true, ite_false] <;> ring
    simp only [J, Kbar, Sbar, ← integral_const_mul]
    simp_rw [h]
    by_cases he : i = j
    · subst j
      simp only [ite_true]
      exact integral_add ((hInt (hKm i i) (hK · i i)).const_mul _)
        ((hInt (hSm i) (hS · i)).const_mul _)
    · simp [he]
  let aX := γ / (2 * Real.sqrt t)
  let aY := γ / (2 * Real.sqrt (1 - t))
  let aV := fun i => γ ^ 2 / 2 * (vX i - vY i)
  let fX := fun (i : ι) ω => aX * (Z ω (.inl i) * S (Z ω) i)
  let fY := fun (i : ι) ω => aY * (Z ω (.inr i) * S (Z ω) i)
  let fV := fun (i : ι) ω => aV i * S (Z ω) i
  let row := fun i => fX i - fY i - fV i
  have hpoint (ω : ΩX × ΩY) : kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω = ∑ i, row i ω := by
    rw [kahaneInterpolatedTestDerivative, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change F' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω))) *
      (finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i * _) = row i ω
    simp only [row, Pi.sub_apply, fX, fY, fV, S, kahaneSumVectorScore, finiteChaosVectorTestScore, aX, aY, aV, Z]
    ring
  have hRowInt (i : ι) : Integrable (row i) μ :=
    (((hZS i (.inl i)).const_mul aX).sub ((hZS i (.inr i)).const_mul aY)).sub
      ((hInt (hSm i) (hS · i)).const_mul (aV i))
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun i _ => hRowInt i]
  refine Finset.sum_nonpos fun i _ => ?_
  have hx : Integrable (fX i) μ := (hZS i (.inl i)).const_mul aX
  have hy : Integrable (fY i) μ := (hZS i (.inr i)).const_mul aY
  have hd : Integrable (fV i) μ := (hInt (hSm i) (hS · i)).const_mul (aV i)
  have heval : (∫ ω, row i ω ∂μ) = aX * (∫ ω, Z ω (.inl i) * S (Z ω) i ∂μ) -
      aY * (∫ ω, Z ω (.inr i) * S (Z ω) i ∂μ) - aV i * Sbar i := by
    calc
      _ = (∫ ω, (fX i - fY i) ω ∂μ) - ∫ ω, fV i ω ∂μ := integral_sub (hx.sub hy) hd
      _ = _ := by rw [integral_sub' hx hy]; simp only [fX, fY, fV, Sbar, integral_const_mul]
  rw [heval, hibp i (.inl i), hibp i (.inr i)]
  have hscale (s : ℝ) (hs : s ≠ 0) (cov : ι → ℝ) :
      γ / (2 * s) * (s * ∑ j, cov j * J i j) = (1 / 2 : ℝ) * ∑ j, cov j * (γ * J i j) := by
    rw [← mul_assoc, show γ / (2 * s) * s = 1 / 2 * γ by field_simp <;> ring, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  dsimp only [aX, aY]
  rw [hscale _ (Real.sqrt_pos.mpr ht).ne', hscale _ (Real.sqrt_pos.mpr (sub_pos.mpr ht1)).ne',
    ← mul_sub, ← Finset.sum_sub_distrib]
  change (1 / 2 : ℝ) * (∑ j, (covX i j * (γ * J i j) - covY i j * (γ * J i j))) - aV i * Sbar i ≤ 0
  have hterm (j : ι) : covX i j * (γ * J i j) - covY i j * (γ * J i j) =
      γ ^ 2 * ((covX i j - covY i j) * Kbar i j) +
        (if i = j then γ ^ 2 * ((covX i i - covY i i) * Sbar i) else 0) := by
    rw [hessian]
    split_ifs with hij
    · subst j; ring
    · ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, aV, hvX, hvY]
  have hK0 (j : ι) : 0 ≤ Kbar i j := by
    apply integral_nonneg
    intro ω
    exact mul_nonneg (mul_nonneg (mul_nonneg (ha i) (Real.exp_nonneg _))
      (mul_nonneg (ha j) (Real.exp_nonneg _))) (hF''nonneg _ (finiteChaosVectorMass_nonneg a v γ ha _))
  have hnonpos : (∑ j, (covX i j - covY i j) * Kbar i j) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hcov i j)) (hK0 j)
  change (1 / 2 : ℝ) * (γ ^ 2 * (∑ j, (covX i j - covY i j) * Kbar i j) + _) -
    γ ^ 2 / 2 * (covX i i - covY i i) * Sbar i ≤ 0
  linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg γ) hnonpos]

end DOZZ.Proofs
