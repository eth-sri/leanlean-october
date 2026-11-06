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

public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- Covariance of two coordinates pulled back from the first factor of a product measure. -/
theorem gaussianCovariance_product_fst
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY) (X : ΩX → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hPY : IsProbabilityMeasure PY)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => X ω.1 i) (fun ω => X ω.1 j) =
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) := by
  let := hX.1
  let := hPY
  simpa only [DOZZ.gaussianCovariance, probReal_univ, one_smul] using
    integral_fun_fst (μ := PX) (ν := PY) (fun ω => X ω i * X ω j)

/-- Covariance of two coordinates pulled back from the second factor of a product measure. -/
theorem gaussianCovariance_product_snd
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY) (Y : ΩY → ι → ℝ)
    (hPX : IsProbabilityMeasure PX) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => Y ω.2 i) (fun ω => Y ω.2 j) =
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) := by
  let := hPX
  let := hY.1
  simpa only [DOZZ.gaussianCovariance, probReal_univ, one_smul] using
    integral_fun_snd (μ := PX) (ν := PY) (fun ω => Y ω i * Y ω j)

variable {ΩX ΩY ι : Type*} [_inst1 : MeasurableSpace ΩX] [_inst2 : MeasurableSpace ΩY] [_inst3 : Fintype ι] [_inst4 : DecidableEq ι] (PX : Measure ΩX) (PY : Measure ΩY) (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ) (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)

include ΩX ΩY ι _inst1 _inst2 _inst3 _inst4 PX PY X Y hX hY
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


/-- Gaussian integration by parts for a smooth Kahane score on the concatenated independent
blocks. This is the reusable Stein step in the finite interpolation argument. -/
theorem kahaneSumVectorScore_gaussian_integration_by_parts
    
    (a v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (c : Sum ι ι → ℝ) (hc : ∀ k, 0 ≤ c k) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z i,
      ‖kahaneSumVectorScore a v γ t F' z i‖ ≤
        M * Real.exp (∑ k, c k * |z k|))
    (hDbound : ∀ z i k,
      ‖kahaneSumVectorScoreDerivative a v γ t F' F'' z i k‖ ≤
        M * Real.exp (∑ k, c k * |z k|))
    (i : ι) (k : Sum ι ι) :
    ∫ ω, (fun ω : ΩX × ΩY =>
        match k with
        | Sum.inl j => X ω.1 j
        | Sum.inr j => Y ω.2 j) ω *
        kahaneSumVectorScore a v γ t F'
          (fun j => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) i ∂(PX.prod PY) =
      ∑ j, DOZZ.gaussianCovariance (PX.prod PY)
          (fun ω => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)
          (fun ω => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) *
        ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F''
          (fun j => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) i j ∂(PX.prod PY) := by
  classical
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω j => match j with
    | Sum.inl l => X ω.1 l
    | Sum.inr l => Y ω.2 l
  have hZ  := independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
  let G  := fun z => kahaneSumVectorScore a v γ t F' z i
  let D  := fun z j =>
    kahaneSumVectorScoreDerivative a v γ t F' F'' z i j
  have hGmeas : Measurable G := by
    dsimp [G, kahaneSumVectorScore, finiteChaosVectorTestScore]
    fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hDmeas : ∀ j, Measurable (fun z => D z j) := by
    intro j
    cases j <;> simp only [D, kahaneSumVectorScoreDerivative,
      kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative] <;>
      split_ifs <;>
      fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hGdir : ∀ (x d : Sum ι ι → ℝ) s,
      HasDerivAt (fun r => G (fun j => x j + r * d j))
        (∑ j, d j * D (fun j => x j + s * d j) j) s := by
    intro x d s
    exact kahaneSumVectorScore_directional_hasDerivAt a v γ t F' F'' hF' x d i s
  have hGbound' : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|) := by
    intro z
    exact hGbound z i
  have hDbound' : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ l, c l * |z l|) := by
    intro z j
    exact hDbound z i j
  have hresult := finite_gaussian_integration_by_parts_of_absExp_bound
    (PX.prod PY) Z hZ k G D hGmeas hDmeas c hc M hM hGbound' hDbound' hGdir
  exact hresult



/-- The smooth Kahane interpolation derivative has nonpositive expectation. The stated
integrability conditions are the finite exponential-envelope consequences needed by Gaussian IBP
and by rearranging the finite sums. -/
theorem kahaneSmoothInterpolation_integrand_nonpos_of_gaussian_ibp
    
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
        γ t F' (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hXScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => X ω.1 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hYScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => Y ω.2 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hKInt : ∀ i j, Integrable
      (fun ω : ΩX × ΩY => finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
        γ (kahaneSumVectorField t (fun k => match k with
          | Sum.inl l => X ω.1 l
          | Sum.inr l => Y ω.2 l)) i *
        finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
          γ (kahaneSumVectorField t (fun k => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)) j *
        F'' (finiteChaosVectorMass a (fun i => t * vX i + (1 - t) * vY i) γ
          (kahaneSumVectorField t (fun k => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)))) (PX.prod PY)) :
    ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY) ≤ 0 := by
  classical
  let  := hX.1
  let  := hY.1
  let μ  := PX.prod PY
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let v  := fun i => t * vX i + (1 - t) * vY i
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
    | Sum.inl i => X ω.1 i
    | Sum.inr i => Y ω.2 i
  let score (ω : ΩX × ΩY) (i : ι) : ℝ :=
    kahaneSumVectorScore a v γ t F' (Z ω) i
  let fieldD (ω : ΩX × ΩY) (i j : ι) : ℝ :=
    kahaneSumVectorFieldScoreDerivative a v γ t F' F'' (Z ω) i j
  let K (ω : ΩX × ΩY) (i j : ι) : ℝ :=
    finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i *
      finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j *
        F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)))
  let Hbar  := fun i j => γ * ∫ ω, fieldD ω i j ∂μ
  let Kbar  := fun i j => ∫ ω, K ω i j ∂μ
  let Dbar  := fun i => ∫ ω, score ω i ∂μ
  let A  := fun i => γ * ∫ ω, X ω.1 i * score ω i ∂μ
  let B  := fun i => γ * ∫ ω, Y ω.2 i * score ω i ∂μ
  have hcross (i j : ι) : DOZZ.gaussianCovariance μ
      (fun ω => Y ω.2 i) (fun ω => X ω.1 j) = 0 := by
    simpa [DOZZ.gaussianCovariance, mul_comm] using
      gaussianCovariance_product_cross_eq_zero PX PY X Y hX hY j i
  have hXibp : ∀ i, A i = Real.sqrt t * ∑ j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) * Hbar i j := by
    intro i
    have hIBP := kahaneSumVectorScore_gaussian_integration_by_parts PX PY X Y hX hY
      a v γ t F' F'' hF'meas hF''meas hF' c hc M hM hGbound hDbound i (Sum.inl i)
    dsimp only [A]
    rw [hIBP, Fintype.sum_sum_type]
    simp only [Z, μ, gaussianCovariance_product_fst PX PY X hX hY.1,
      gaussianCovariance_product_cross_eq_zero PX PY X Y hX hY,
      kahaneSumVectorScoreDerivative, integral_const_mul, Hbar, fieldD,
      Finset.mul_sum, zero_mul, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hYibp : ∀ i, B i = Real.sqrt (1 - t) * ∑ j,
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) * Hbar i j := by
    intro i
    have hIBP := kahaneSumVectorScore_gaussian_integration_by_parts PX PY X Y hX hY
      a v γ t F' F'' hF'meas hF''meas hF' c hc M hM hGbound hDbound i (Sum.inr i)
    dsimp only [B]
    rw [hIBP, Fintype.sum_sum_type]
    simp only [Z, μ,
      gaussianCovariance_product_snd PX PY Y hX.1 hY,
      hcross,
      kahaneSumVectorScoreDerivative, integral_const_mul, Hbar, fieldD,
      Finset.mul_sum, zero_mul, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hHessian : ∀ i j, Hbar i j = γ ^ 2 * Kbar i j +
      if i = j then γ ^ 2 * Dbar i else 0 := by
    intro i j
    have hpoint (ω : ΩX × ΩY) : γ * fieldD ω i j =
        γ ^ 2 * K ω i j + if i = j then γ ^ 2 * score ω i else 0 := by
      simp only [fieldD, kahaneSumVectorFieldScoreDerivative,
        finiteChaosVectorTestScoreDerivative, score, K, kahaneSumVectorScore,
        finiteChaosVectorTestScore]
      split_ifs <;> ring
    dsimp only [Hbar, Kbar, Dbar]
    rw [← integral_const_mul]
    simp_rw [hpoint]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      rw [integral_add ((hKInt i i).const_mul _) ((hScoreInt i).const_mul _),
        integral_const_mul, integral_const_mul]
    · simp [hij, integral_const_mul]
  have hKnonneg : ∀ i j, 0 ≤ Kbar i j := by
    intro i j
    apply integral_nonneg
    intro ω
    have hwi : 0 ≤ finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i :=
      mul_nonneg (ha i) (Real.exp_nonneg _)
    have hwj : 0 ≤ finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j :=
      mul_nonneg (ha j) (Real.exp_nonneg _)
    exact mul_nonneg (mul_nonneg hwi hwj)
      (hF''nonneg _ (Finset.sum_nonneg fun i _ =>
        mul_nonneg (ha i) (Real.exp_nonneg _)))
  have hderivIdentity :
      ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂μ =
        (∑ i, A i) / (2 * Real.sqrt t) -
        (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (vX i - vY i) * Dbar i := by
    let T (i : ι) (ω : ΩX × ΩY) :=
      γ / (2 * Real.sqrt t) * (X ω.1 i * score ω i) -
      γ / (2 * Real.sqrt (1 - t)) * (Y ω.2 i * score ω i) -
      γ ^ 2 / 2 * (vX i - vY i) * score ω i
    have hpoint (ω : ΩX × ΩY) :
        kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω = ∑ i, T i ω := by
      rw [kahaneInterpolatedTestDerivative]
      have hmass : kahaneInterpolatedMass X Y vX vY a γ t ω =
          finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)) := by
        abel
      have hweight (i : ι) :
          a i * Real.exp (γ * (Real.sqrt t * X ω.1 i +
            Real.sqrt (1 - t) * Y ω.2 i) -
            γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) =
          finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i := by
        abel
      rw [hmass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [T, score, kahaneSumVectorScore, finiteChaosVectorTestScore]
      rw [hweight i]
      ring
    have htermInt (i : ι) : Integrable (T i) μ :=
      (((hXScoreInt i).const_mul _).sub ((hYScoreInt i).const_mul _)).sub
        ((hScoreInt i).const_mul _)
    calc
      _ = ∫ ω, ∑ i, T i ω ∂μ := integral_congr_ae (ae_of_all μ hpoint)
      _ = ∑ i, ∫ ω, T i ω ∂μ := integral_finsetSum _ (fun i _ => htermInt i)
      _ = ∑ i, (A i / (2 * Real.sqrt t) - B i / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * (vX i - vY i) * Dbar i) := by
        apply Finset.sum_congr rfl
        intro i _
        have h1 := (hXScoreInt i).const_mul (γ / (2 * Real.sqrt t))
        have h2 := (hYScoreInt i).const_mul (γ / (2 * Real.sqrt (1 - t)))
        have h3 := (hScoreInt i).const_mul (γ ^ 2 / 2 * (vX i - vY i))
        dsimp only [T, A, B, Dbar]
        rw [integral_sub (f := fun ω =>
          γ / (2 * Real.sqrt t) * (X ω.1 i * score ω i) -
          γ / (2 * Real.sqrt (1 - t)) * (Y ω.2 i * score ω i))
          (h1.sub h2) h3, integral_sub h1 h2]
        simp only [integral_const_mul]
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum, mul_assoc]
  have hsign := kahaneInterpolation_derivative_nonpos_of_covariance_order γ t
    (fun i j => DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j))
    (fun i j => DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    A B Hbar Kbar Dbar ht ht1 hcov hKnonneg hXibp hYibp hHessian
  have hdiag : (∑ i, (vX i - vY i) * Dbar i) =
      ∑ i, (DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i)) * Dbar i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvX i, hvY i]
  rw [hderivIdentity, hdiag]
  exact hsign
omit ΩX ΩY ι _inst1 _inst2 _inst3 _inst4 PX PY X Y hX hY


end DOZZ.Proofs
