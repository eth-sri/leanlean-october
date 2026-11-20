module

public import NearlyMinimax.GaussianMonomialProducts

@[expose] public section

/-! Genuine product Gaussian mark amplitudes: measurability, integrability,
and exponential coefficient cost, with no prescribed tensor budget. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def gaussianPrimitiveScalar (d : ℕ) (lam : ℝ) (e : GaussianPrimitiveMark d) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1

section
variable (d : ℕ) (lam : ℝ)

theorem gaussianPrimitiveScalar_measurable :
    Measurable (gaussianPrimitiveScalar d lam) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun Z : Covariate d => lam / 2 * gaussianHermite h.1.1 h.1.2 Z)
  have hm : Measurable (fun Z : Covariate d => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact hm.const_mul _

theorem gaussianPrimitiveScalar_slice_integrable (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveScalar d lam (Z, h)) (standardGaussianPi d) := (gaussianHermite_integrable h.1.1 h.1.2).const_mul _

theorem gaussianPrimitiveScalar_integrable :
    Integrable (gaussianPrimitiveScalar d lam) (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveScalar_measurable d lam).comp (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveScalar_slice_integrable d lam)

theorem gaussianPrimitiveScalar_abs_integral :
    (∫ e, |gaussianPrimitiveScalar d lam e| ∂gaussianPrimitiveMeasure d) ≤
      8 * |lam| * (d : ℝ) ^ 2 := by
  have hs (h : GaussianPrimitiveIndex d) :
      (∫ Z, |gaussianPrimitiveScalar d lam (Z, h)| ∂standardGaussianPi d) ≤ |lam| := by
    change (∫ Z, |lam / 2 * gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ |lam|
    simp only [abs_mul, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (standardGaussian_hermite_abs_integral_le_two h.1.1 h.1.2)
      (abs_nonneg (lam / 2))
    simp_all [abs_div]
  rw [gaussianPrimitiveMeasure, integral_prod_symm _ (gaussianPrimitiveScalar_integrable d lam).abs,
    integral_count]
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h)
  convert hm using 1 <;> simp [GaussianPrimitiveIndex, Fintype.card_prod, pow_two] <;> ring

end

abbrev GaussianTensorMark (κ : Type*) (d : ℕ) := κ → GaussianPrimitiveMark d

def gaussianTensorMeasure (κ : Type*) [Fintype κ] (d : ℕ) : Measure (GaussianTensorMark κ d) :=
  Measure.pi (fun _ => gaussianPrimitiveMeasure d)

def gaussianTensorScalar {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveScalar d lam (e i)

def gaussianTensorLeftPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)

def gaussianTensorRightPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2)

def gaussianTensorFrameAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) : ℝ :=
  gaussianTensorScalar lam e * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'

theorem gaussianTensorMeasure_finite (κ : Type*) [Fintype κ] (d : ℕ) :
    IsFiniteMeasure (gaussianTensorMeasure κ d) := by
  unfold gaussianTensorMeasure
  infer_instance

section
variable {κ : Type*} [Fintype κ]

section
variable {d : ℕ}

theorem gaussianTensorScalar_measurable (lam : ℝ) :
    Measurable (gaussianTensorScalar (κ := κ) (d := d) lam) :=
  Finset.measurable_fun_prod _ (fun i _ =>
    (gaussianPrimitiveScalar_measurable d lam).comp (measurable_pi_apply i))

theorem gaussianTensorScalar_integrable (lam : ℝ) :
    Integrable (gaussianTensorScalar (κ := κ) (d := d) lam) (gaussianTensorMeasure κ d) :=
  Integrable.fintype_prod (fun _ : κ => gaussianPrimitiveScalar_integrable d lam)

theorem gaussianTensorScalar_abs_integral (lam : ℝ) :
    (∫ e, |gaussianTensorScalar (κ := κ) (d := d) lam e| ∂gaussianTensorMeasure κ d) ≤
      (8 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
  unfold gaussianTensorScalar gaussianTensorMeasure
  simp only [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (fun (_ : κ) e => |gaussianPrimitiveScalar d lam e|)]
  calc
    _ ≤ ∏ _i : κ, (8 * |lam| * (d : ℝ) ^ 2) := Finset.prod_le_prod₀
      (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
      (fun _ _ => gaussianPrimitiveScalar_abs_integral d lam)
    _ = _ := by simp

theorem gaussianTensorPolynomial_coeff_measurable
    (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) (β : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianTensorMark κ d =>
      (gaussianPolynomialProduct (fun i => a (e i).2) (fun i => s (e i).2)).coeff β) := by
  have hf : Measurable (fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct (fun i => a (h i)) (fun i => s (h i))).coeff β) := measurable_of_countable _
  apply hf.comp <;> fun_prop

end

section
variable {d D : ℕ} (lam : ℝ)

theorem gaussianTensorFrameAmplitude_measurable
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorFrameAmplitude lam e β β') := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.1) (fun h => h.2.1.1) (polynomialBoxExponent β.val)
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.2) (fun h => h.2.1.2) (polynomialBoxExponent β'.val)
  exact ((gaussianTensorScalar_measurable lam).mul hl).mul hr

theorem gaussianTensorFrameAmplitude_cost_bound
    (e : GaussianTensorMark κ d) :
    separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e ≤
      |gaussianTensorScalar lam e| * (8 : ℝ) ^ (2 * Fintype.card κ) := by
  have h := gaussianPolynomialProduct_rankone_cost (D := D)
    (fun i : κ => (e i).2.1.1) (fun i => (e i).2.2.1.1)
    (fun i : κ => (e i).2.1.2) (fun i => (e i).2.2.1.2) (gaussianTensorScalar lam e)
  simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
    gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using h

end

end

def gaussianTensorAmplitude {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) : ℝ :=
  gaussianTensorScalar lam e * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'

def gaussianTensorObservable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (t : κ → ℝ)
    (x y : κ → Covariate d) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveLeft lam (t i) (e i) (x i) * gaussianPrimitiveRight lam (t i) (e i) (y i)

def realMatrixSymmetrize {I : Type*} (A : I → I → ℝ) (i j : I) : ℝ := (A i j + A j i) / 2

theorem separatedMatrixCost_symmetrize_le {E I : Type*} [Fintype I] [DecidableEq I]
    (A : E → I → I → ℝ) (e : E) :
    separatedMatrixCost (fun e => realMatrixSymmetrize (A e)) e ≤ separatedMatrixCost A e := by
  have hp (i j : I) : |realMatrixSymmetrize (A e) i j| ≤ (|A e i j| + |A e j i|) / 2 := by
    grind [realMatrixSymmetrize]
  calc
    _ ≤ ∑ i : I, ∑ j : I, (|A e i j| + |A e j i|) / 2 := Finset.sum_le_sum
      (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = separatedMatrixCost A e := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : I => |A e j i|)]
      unfold separatedMatrixCost
      ring

def gaussianTensorSymmetricAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e)

section
variable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)

theorem gaussianTensorSymmetricAmplitude_measurable
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorSymmetricAmplitude lam e β β') :=
  ((gaussianTensorFrameAmplitude_measurable lam β β').add
    (gaussianTensorFrameAmplitude_measurable lam β' β)).div_const 2

theorem gaussianTensorSymmetricAmplitude_moments :
    SeparatedMatrixIntegrable (gaussianTensorMeasure κ d)
      (gaussianTensorSymmetricAmplitude (D := D) lam) ∧
    (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
  let K := (8 : ℝ) ^ (2 * Fintype.card κ)
  have hi : Integrable (fun e => |gaussianTensorScalar lam e| * K) (gaussianTensorMeasure κ d) :=
    (gaussianTensorScalar_integrable lam).abs.mul_const K
  have hle (e : GaussianTensorMark κ d) : separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e ≤
      |gaussianTensorScalar lam e| * K :=
    (separatedMatrixCost_symmetrize_le _ e).trans (gaussianTensorFrameAmplitude_cost_bound lam e)
  have hA := SeparatedMatrixIntegrable.of_cost_le (gaussianTensorSymmetricAmplitude_measurable lam) hi hle
  refine ⟨hA, (integral_mono hA.cost hi hle).trans ?_⟩
  rw [integral_mul_const]
  apply (mul_le_mul_of_nonneg_right (gaussianTensorScalar_abs_integral lam) (by dsimp [K]; positivity)).trans_eq
  dsimp [K]
  rw [pow_mul, ← mul_pow]
  ring

end

end NearlyMinimax
