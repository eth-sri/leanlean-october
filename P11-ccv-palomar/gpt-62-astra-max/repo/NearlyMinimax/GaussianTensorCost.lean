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

section
variable (κ : Type*) (d : ℕ) (lam : ℝ)

instance gaussianPrimitiveMeasure_isFinite : IsFiniteMeasure (gaussianPrimitiveMeasure d) :=
  gaussianPrimitiveMeasure_finite d

def gaussianPrimitiveScalar (e : GaussianPrimitiveMark d) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1

theorem gaussianPrimitiveScalar_measurable :
    Measurable (gaussianPrimitiveScalar d lam) := by
  apply measurable_from_prod_countable_left
  intro h
  have hm : Measurable (fun Z => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact hm.const_mul _

theorem gaussianPrimitiveScalar_slice_integrable (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveScalar d lam (Z, h)) (standardGaussianPi d) := (gaussianHermite_integrable h.1.1 h.1.2).const_mul _

theorem gaussianPrimitiveScalar_integrable :
    Integrable (gaussianPrimitiveScalar d lam) (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable
    (fun h => (gaussianPrimitiveScalar_measurable d lam).comp (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveScalar_slice_integrable d lam)

theorem gaussianPrimitiveScalar_abs_integral :
    (∫ e, |gaussianPrimitiveScalar d lam e| ∂gaussianPrimitiveMeasure d) ≤
      8 * |lam| * d ^ 2 := by
  have hs h :
      (∫ Z, |gaussianPrimitiveScalar d lam (Z, h)| ∂standardGaussianPi d) ≤ |lam| := by
    change (∫ Z, |lam / 2 * gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ _
    simp [abs_mul, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (standardGaussian_hermite_abs_integral_le_two h.1.1 h.1.2)
      (abs_nonneg (lam / 2))
    grind
  rw [gaussianPrimitiveMeasure, integral_prod_symm _ (gaussianPrimitiveScalar_integrable d lam).abs,
    integral_count]
  convert (Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h)) using 1 <;> simp <;> ring

abbrev GaussianTensorMark := κ → GaussianPrimitiveMark d

def gaussianTensorMeasure [Fintype κ] (d : ℕ) : Measure (GaussianTensorMark κ d) :=
  Measure.pi (fun _ => gaussianPrimitiveMeasure d)

end

section
variable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)

def gaussianTensorScalar (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveScalar d lam (e i)

def gaussianTensorLeftPolynomial (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)

def gaussianTensorRightPolynomial (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2)

def gaussianTensorFrameAmplitude
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) : ℝ :=
  gaussianTensorScalar lam e * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'

theorem gaussianTensorMeasure_finite (κ : Type*) [Fintype κ] (d : ℕ) :
    IsFiniteMeasure (gaussianTensorMeasure κ d) := by
  letI  := gaussianPrimitiveMeasure_finite d
  unfold gaussianTensorMeasure
  infer_instance

theorem gaussianTensorScalar_measurable :
    Measurable (gaussianTensorScalar (κ := κ) (d := d) lam) :=
  Finset.measurable_fun_prod _ (fun i _ =>
    (gaussianPrimitiveScalar_measurable d lam).comp (measurable_pi_apply i))

theorem gaussianTensorScalar_integrable :
    Integrable (gaussianTensorScalar lam) (gaussianTensorMeasure κ d) :=
  Integrable.fintype_prod (fun _ => gaussianPrimitiveScalar_integrable d lam)

theorem gaussianTensorScalar_abs_integral :
    (∫ e, |gaussianTensorScalar lam e| ∂gaussianTensorMeasure κ d) ≤
      (8 * |lam| * d ^ 2) ^ Fintype.card κ := by
  unfold gaussianTensorScalar gaussianTensorMeasure
  simp [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (fun _ e => |gaussianPrimitiveScalar d lam e|)]
  calc
    _ ≤ _ := Finset.prod_le_prod₀
      (fun _ _ => by positivity)
      (fun _ _ => gaussianPrimitiveScalar_abs_integral d lam)
    _ = _ := by simp

theorem gaussianTensorPolynomial_coeff_measurable
    (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) (β : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianTensorMark κ d =>
      (gaussianPolynomialProduct (fun i => a (e i).2) (fun i => s (e i).2)).coeff β) := by
  have hf : Measurable (fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct (a ∘ h) (s ∘ h)).coeff β) := measurable_of_countable _
  exact hf.comp (by fun_prop)

theorem gaussianTensorFrameAmplitude_measurable
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorFrameAmplitude lam e β β') := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ)
    (fun h => h.1.1) (fun h => h.2.1.1) (polynomialBoxExponent β.val)
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ)
    (fun h => h.1.2) (fun h => h.2.1.2) (polynomialBoxExponent β'.val)
  exact ((gaussianTensorScalar_measurable lam).mul hl).mul hr

theorem gaussianTensorFrameAmplitude_cost_bound
    (e : GaussianTensorMark κ d) :
    separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e ≤
      |gaussianTensorScalar lam e| * 8 ^ (2 * Fintype.card κ) := by
  have h := gaussianPolynomialProduct_rankone_cost (D := D)
    (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)
    (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2) (gaussianTensorScalar lam e)
  simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
    gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using h

theorem gaussianTensorFrameAmplitude_cost_measurable :
    Measurable (separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam)) := Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (gaussianTensorFrameAmplitude_measurable lam β β').abs))

theorem gaussianTensorFrameAmplitude_cost_integrable :
    Integrable (separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  apply ((gaussianTensorScalar_integrable lam).abs.mul_const
    (8 ^ (2 * Fintype.card κ))).mono'
    (gaussianTensorFrameAmplitude_cost_measurable lam).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => by positivity))]
  exact gaussianTensorFrameAmplitude_cost_bound lam e

theorem gaussianTensorFrameAmplitude_integrated_cost :
    (∫ e, separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * d ^ 2) ^ Fintype.card κ := by
  have hm := integral_mono (gaussianTensorFrameAmplitude_cost_integrable (D := D) lam)
    ((gaussianTensorScalar_integrable (d := d) lam).abs.mul_const (8 ^ (2 * Fintype.card κ)))
    (gaussianTensorFrameAmplitude_cost_bound lam)
  rw [integral_mul_const] at hm
  have h := mul_le_mul_of_nonneg_right (gaussianTensorScalar_abs_integral (κ := κ) (d := d) lam)
    (by positivity : 0 ≤ (8 : ℝ) ^ (2 * Fintype.card κ))
  apply hm.trans
  apply h.trans_eq
  rw [pow_mul, ← mul_pow]
  ring

def gaussianTensorAmplitude
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) : ℝ :=
  gaussianTensorScalar lam e * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'

def gaussianTensorObservable (t : κ → ℝ)
    (x y : κ → Covariate d) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveLeft lam (t i) (e i) (x i) * gaussianPrimitiveRight lam (t i) (e i) (y i)

end

def realMatrixSymmetrize {I : Type*} (A : I → I → ℝ) (i j : I) : ℝ := (A i j + A j i) / 2

theorem separatedMatrixCost_symmetrize_le {E I : Type*} [Fintype I] [DecidableEq I]
    (A : E → I → I → ℝ) (e : E) :
    separatedMatrixCost (fun e => realMatrixSymmetrize (A e)) e ≤ separatedMatrixCost A e := by
  have hp i j : |realMatrixSymmetrize (A e) i j| ≤ (|A e i j| + |A e j i|) / 2 := by
    unfold realMatrixSymmetrize
    grind
  calc
    _ ≤ _ := Finset.sum_le_sum
      (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => |A e j i|)]
      unfold separatedMatrixCost
      ring

variable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)

def gaussianTensorSymmetricAmplitude
    (e : GaussianTensorMark κ d) : HighFrameIndex d D → HighFrameVector d D :=
  realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e)

theorem gaussianTensorSymmetricAmplitude_measurable
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorSymmetricAmplitude lam e β β') :=
  ((gaussianTensorFrameAmplitude_measurable lam β β').add
    (gaussianTensorFrameAmplitude_measurable lam β' β)).div_const 2

theorem gaussianTensorSymmetricAmplitude_cost_integrable :
    Integrable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  apply (gaussianTensorFrameAmplitude_cost_integrable lam).mono'
    (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _ (fun β' _ => (gaussianTensorSymmetricAmplitude_measurable lam β β').abs))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => by positivity))]
  exact separatedMatrixCost_symmetrize_le _ e

theorem gaussianTensorSymmetricAmplitude_integrated_cost :
    (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * d ^ 2) ^ Fintype.card κ :=
  (integral_mono (gaussianTensorSymmetricAmplitude_cost_integrable lam)
    (gaussianTensorFrameAmplitude_cost_integrable lam)
    (separatedMatrixCost_symmetrize_le _)).trans (gaussianTensorFrameAmplitude_integrated_cost lam)

end NearlyMinimax
