/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestGrowth
public import DOZZ.GMC.FiniteChaosLaplaceBounds
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

variable {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι] [DecidableEq ι]


private lemma cov_comp_mp {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    {μ : Measure Ω} {ν : Measure Ω'} {p : Ω → Ω'} (hp : MeasurePreserving p μ ν)
    (W : Ω' → ι → ℝ) (hW : IsCenteredJointlyGaussian ν W) (i j : ι) :
    DOZZ.gaussianCovariance μ (fun ω => W (p ω) i) (fun ω => W (p ω) j) =
      DOZZ.gaussianCovariance ν (fun x => W x i) (fun x => W x j) := by
  classical
  have hi : MemLp (fun x => W x i) 2 ν := by simpa [Pi.single_apply] using (hW.2.2 (Pi.single i 1)).1
  have hj : MemLp (fun x => W x j) 2 ν := by simpa [Pi.single_apply] using (hW.2.2 (Pi.single j 1)).1
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hint : Integrable (fun x => W x i * W x j) (μ.map p) := by
    rw [hp.map_eq]; exact memLp_one_iff_integrable.mp (by convert hi.mul hj (hpqr := hH) using 1)
  have hmap := integral_map hp.aemeasurable hint.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  simpa [DOZZ.gaussianCovariance] using hmap.symm

private lemma cov_product_concat (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : Sum ι ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => match i with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k)
        (fun ω => match j with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k) =
      match i, j with
      | Sum.inl k, Sum.inl l => DOZZ.gaussianCovariance PX (fun ω => X ω k) (fun ω => X ω l)
      | Sum.inr k, Sum.inr l => DOZZ.gaussianCovariance PY (fun ω => Y ω k) (fun ω => Y ω l)
      | _, _ => 0 := by
  let _ := hX.1; let _ := hY.1
  have hcross (a b : ι) : DOZZ.gaussianCovariance (PX.prod PY) (fun ω => X ω.1 a) (fun ω => Y ω.2 b) = 0 := by
    rw [DOZZ.gaussianCovariance, integral_prod_mul (fun x => X x a) (fun y => Y y b),
      coord_mean PX X hX a, coord_mean PY Y hY b]; simp
  cases i <;> cases j
  · exact cov_comp_mp measurePreserving_fst X hX _ _
  · exact hcross _ _
  · simpa [DOZZ.gaussianCovariance, mul_comm] using hcross _ _
  · exact cov_comp_mp measurePreserving_snd Y hY _ _


/-- The smooth Kahane interpolation derivative has nonpositive expectation. -/
theorem kahaneSmoothInterpolation_integrand_nonpos_of_gaussian_ibp

    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a vX vY : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ t : ℝ)
    (F' F'' : ℝ → ℝ)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x)
    (ht : 0 < t) (ht1 : t < 1)
    (hvX : ∀ i, vX i = DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i))
    (hvY : ∀ i, vY i = DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i))
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    (c : Sum ι ι → ℝ) (hc : ∀ k, 0 ≤ c k) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z i,
      ‖kahaneSumVectorScore a (fun i => t * vX i + (1 - t) * vY i)
          γ t F' z i‖ ≤ M * Real.exp (∑ k, c k * |z k|))
    (hDbound : ∀ z i k,
      ‖kahaneSumVectorScoreDerivative a (fun i => t * vX i + (1 - t) * vY i)
          γ t F' F'' z i k‖ ≤ M * Real.exp (∑ k, c k * |z k|))
    (hScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => kahaneSumVectorScore a (fun i => t * vX i + (1 - t) * vY i)
        γ t F' (fun k => match k with | Sum.inl j => X ω.1 j | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hXScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => X ω.1 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with | Sum.inl j => X ω.1 j | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hYScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => Y ω.2 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with | Sum.inl j => X ω.1 j | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (_hFieldDInt : ∀ i j, Integrable
      (fun ω : ΩX × ΩY => kahaneSumVectorFieldScoreDerivative a
        (fun i => t * vX i + (1 - t) * vY i) γ t F' F''
        (fun k => match k with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l) i j) (PX.prod PY))
    (hKInt : ∀ i j, Integrable
      (fun ω : ΩX × ΩY => finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
        γ (kahaneSumVectorField t (fun k => match k with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l)) i *
        finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
          γ (kahaneSumVectorField t (fun k => match k with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l)) j *
        F'' (finiteChaosVectorMass a (fun i => t * vX i + (1 - t) * vY i) γ
          (kahaneSumVectorField t (fun k => match k with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l))))
      (PX.prod PY)) :
    ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY) ≤ 0 := by
  have score_ibp (v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ) (hF'meas : Measurable F') (hF''meas : Measurable F'') (hF' : ∀ x, HasDerivAt F' (F'' x) x) (c : Sum ι ι → ℝ) (hc : ∀ k, 0 ≤ c k) (M : ℝ) (hM : 0 ≤ M) (hGbound : ∀ z i, ‖kahaneSumVectorScore a v γ t F' z i‖ ≤ M * Real.exp (∑ k, c k * |z k|)) (hDbound : ∀ z i k, ‖kahaneSumVectorScoreDerivative a v γ t F' F'' z i k‖ ≤ M * Real.exp (∑ k, c k * |z k|)) (i : ι) (k : Sum ι ι) : ∫ ω, (match k with | Sum.inl j => X ω.1 j | Sum.inr j => Y ω.2 j) *
          kahaneSumVectorScore a v γ t F' (fun j => match j with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l) i
          ∂(PX.prod PY) =
        ∑ j, DOZZ.gaussianCovariance (PX.prod PY)
            (fun ω => match k with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l)
            (fun ω => match j with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l) *
          ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F''
            (fun j => match j with | Sum.inl l => X ω.1 l | Sum.inr l => Y ω.2 l) i j ∂(PX.prod PY) := by
    have hZ := independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
    have hGmeas : Measurable fun z => kahaneSumVectorScore a v γ t F' z i := by
      dsimp [kahaneSumVectorScore, finiteChaosVectorTestScore]
      fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
    have hDmeas (j : Sum ι ι) : Measurable fun z => kahaneSumVectorScoreDerivative a v γ t F' F'' z i j := by
      cases j with
      | inl j =>
        by_cases hij : i = j <;>
          simp [kahaneSumVectorScoreDerivative, kahaneSumVectorFieldScoreDerivative,
            finiteChaosVectorTestScoreDerivative, hij] <;>
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
      | inr j =>
        by_cases hij : i = j <;>
          simp [kahaneSumVectorScoreDerivative, kahaneSumVectorFieldScoreDerivative,
            finiteChaosVectorTestScoreDerivative, hij] <;>
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
    exact finite_gaussian_integration_by_parts_of_absExp_bound (PX.prod PY) _ hZ k
      (fun z => kahaneSumVectorScore a v γ t F' z i)
      (fun z j => kahaneSumVectorScoreDerivative a v γ t F' F'' z i j)
      hGmeas hDmeas c hc M hM (fun z => hGbound z i) (fun z j => hDbound z i j)
      fun x d s => kahaneSumVectorScore_directional_hasDerivAt a v γ t F' F'' hF' x d i s
  let _ := hX.1; let _ := hY.1
  let μ := PX.prod PY
  let v : ι → ℝ := fun i => t * vX i + (1 - t) * vY i
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with | Sum.inl i => X ω.1 i | Sum.inr i => Y ω.2 i
  let score (ω : ΩX × ΩY) (i : ι) := kahaneSumVectorScore a v γ t F' (Z ω) i
  let fieldD (ω : ΩX × ΩY) (i j : ι) := kahaneSumVectorFieldScoreDerivative a v γ t F' F'' (Z ω) i j
  let K (ω : ΩX × ΩY) (i j : ι) :=
    finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i *
      finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j *
        F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)))
  let Hbar (i j : ι) := γ * ∫ ω, fieldD ω i j ∂μ
  let Kbar (i j : ι) := ∫ ω, K ω i j ∂μ
  let Dbar (i : ι) := ∫ ω, score ω i ∂μ
  let A (i : ι) := γ * ∫ ω, X ω.1 i * score ω i ∂μ
  let B (i : ι) := γ * ∫ ω, Y ω.2 i * score ω i ∂μ
  have hXibp (i : ι) : A i = Real.sqrt t * ∑ j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) * Hbar i j := by
    have hIBP := score_ibp v γ t F' F'' hF'meas hF''meas hF' c hc M hM
      hGbound hDbound i (Sum.inl i)
    dsimp only [A, score, Hbar]
    rw [hIBP, Fintype.sum_sum_type]
    have hr : (∑ j, DOZZ.gaussianCovariance μ (fun ω => Z ω (Sum.inl i)) (fun ω => Z ω (Sum.inr j)) *
        ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i (Sum.inr j) ∂μ) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [cov_product_concat PX PY X Y hX hY (Sum.inl i) (Sum.inr j)]; simp
    rw [hr, add_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cov_product_concat PX PY X Y hX hY (Sum.inl i) (Sum.inl j)]
    simp only [fieldD, kahaneSumVectorScoreDerivative, integral_const_mul]; ring
  have hYibp (i : ι) : B i = Real.sqrt (1 - t) * ∑ j,
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) * Hbar i j := by
    have hIBP := score_ibp v γ t F' F'' hF'meas hF''meas hF' c hc M hM
      hGbound hDbound i (Sum.inr i)
    dsimp only [B, score, Hbar]
    rw [hIBP, Fintype.sum_sum_type]
    have hl : (∑ j, DOZZ.gaussianCovariance μ (fun ω => Z ω (Sum.inr i)) (fun ω => Z ω (Sum.inl j)) *
        ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i (Sum.inl j) ∂μ) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [cov_product_concat PX PY X Y hX hY (Sum.inr i) (Sum.inl j)]; simp
    rw [hl, zero_add, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cov_product_concat PX PY X Y hX hY (Sum.inr i) (Sum.inr j)]
    simp only [fieldD, kahaneSumVectorScoreDerivative, integral_const_mul]; ring
  have hHessian (i j : ι) : Hbar i j = γ ^ 2 * Kbar i j + if i = j then γ ^ 2 * Dbar i else 0 := by
    have hpt (ω : ΩX × ΩY) : γ * fieldD ω i j =
        γ ^ 2 * K ω i j + if i = j then γ ^ 2 * score ω i else 0 := by
      simp only [fieldD, kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative]
      by_cases hij : i = j
      · subst hij; dsimp [score, K, kahaneSumVectorScore, finiteChaosVectorTestScore]; simp; ring
      · simp only [ite_eq_right hij]; dsimp [score, K, kahaneSumVectorScore, finiteChaosVectorTestScore]; ring
    dsimp only [Hbar, Kbar, Dbar]
    rw [← integral_const_mul, integral_congr_ae (ae_of_all μ hpt)]
    by_cases hij : i = j
    · subst hij; simp only [ite_true]
      have hi1 : Integrable (fun ω => γ ^ 2 * K ω i i) μ := (hKInt i i).const_mul _
      have hi2 : Integrable (fun ω => γ ^ 2 * score ω i) μ := (hScoreInt i).const_mul _
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
    · simp only [ite_eq_right hij, add_zero, integral_const_mul]
  have hKnonneg (i j : ι) : 0 ≤ Kbar i j := integral_nonneg fun ω =>
    mul_nonneg (mul_nonneg (mul_nonneg (ha i) (Real.exp_nonneg _)) (mul_nonneg (ha j) (Real.exp_nonneg _)))
      (hF''nonneg _ (finiteChaosVectorMass_nonneg a v γ ha (kahaneSumVectorField t (Z ω))))
  have hderiv : ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂μ =
      (∑ i, A i) / (2 * Real.sqrt t) - (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (vX i - vY i) * Dbar i := by
    have hpt (ω : ΩX × ΩY) : kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω =
        ∑ i, ((γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
          (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i) -
          (γ ^ 2 / 2 * (vX i - vY i)) * score ω i) := by
      rw [kahaneInterpolatedTestDerivative]
      have hm : kahaneInterpolatedMass X Y vX vY a γ t ω =
          finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)) := by
        simp [kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight,
          kahaneSumVectorField, Z, v, mul_comm]
      rw [hm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hw : a i * Real.exp (γ * (Real.sqrt t * X ω.1 i + Real.sqrt (1 - t) * Y ω.2 i) -
          γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) =
          finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i := by
        simp [finiteChaosVectorWeight, kahaneSumVectorField, Z, v]
      simp only [score, kahaneSumVectorScore, finiteChaosVectorTestScore]; rw [hw]; ring
    have hiX (i : ι) : Integrable (fun ω => (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i)) μ :=
      (hXScoreInt i).const_mul _
    have hiY (i : ι) : Integrable (fun ω => (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i)) μ :=
      (hYScoreInt i).const_mul _
    have hiD (i : ι) : Integrable (fun ω => (γ ^ 2 / 2 * (vX i - vY i)) * score ω i) μ :=
      (hScoreInt i).const_mul _
    have hiXY (i : ι) : Integrable (fun ω => (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
        (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i)) μ := (hiX i).sub (hiY i)
    have hiterm (i : ι) : Integrable (fun ω => (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
        (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i) -
        (γ ^ 2 / 2 * (vX i - vY i)) * score ω i) μ := (hiXY i).sub (hiD i)
    rw [integral_congr_ae (ae_of_all μ hpt), integral_finsetSum Finset.univ fun i _ => hiterm i]
    have hev (i : ι) : (∫ ω, (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
        (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i) -
        (γ ^ 2 / 2 * (vX i - vY i)) * score ω i ∂μ) =
        A i / (2 * Real.sqrt t) - B i / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * ((vX i - vY i) * Dbar i) := by
      rw [integral_sub (hiXY i) (hiD i), integral_sub (hiX i) (hiY i),
        integral_const_mul, integral_const_mul, integral_const_mul]
      dsimp only [A, B, Dbar]; ring
    simp_rw [hev, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hderiv]
  have hsign := kahaneInterpolation_derivative_nonpos_of_covariance_order γ t
    (fun i j => DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j))
    (fun i j => DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    A B Hbar Kbar Dbar ht ht1 hcov hKnonneg hXibp hYibp hHessian
  simpa only [show (∑ i, (vX i - vY i) * Dbar i) =
    ∑ i, (DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i) -
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i)) * Dbar i by
    refine Finset.sum_congr rfl fun i _ => by rw [hvX i, hvY i]] using hsign

end DOZZ.Proofs
