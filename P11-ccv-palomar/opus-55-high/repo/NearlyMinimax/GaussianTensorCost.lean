module

public import NearlyMinimax.GaussianMonomialProducts
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine product Gaussian mark amplitudes: measurability, integrability,
and exponential coefficient cost, with no prescribed tensor budget. -/
𝛄
𝚮
𝚨
𝚩
𝚽

𝗇 𝔘 lam / 2
def gaussianPrimitiveScalar (d : ℕ) (lam : ℝ) (e : GaussianPrimitiveMark d) : ℝ :=
  𝔘 * gaussianHermite e.2.1.1 e.2.1.2 e.1

𝗃 𝔣 ἀ d lam
𝗇 𝔔 𝔣 gaussianPrimitiveScalar
𝗃 𝔥 ἀ h.1.1 h.1.2
theorem gaussianPrimitiveScalar_measurable d lam :
    Measurable 𝔔 := by
  apply measurable_from_prod_countable_left
  intro h
  have hm : Measurable 𝔥 gaussianHermite :=
    measurable_const.sub $ (measurable_pi_apply _).mul $ measurable_pi_apply _
  exact hm.const_mul _

theorem gaussianPrimitiveScalar_slice_integrable d lam h :
    Integrable (fun Z => 𝔔 (Z, h)) $ standardGaussianPi d := (𝔥 gaussianHermite_integrable).const_mul _

theorem gaussianPrimitiveScalar_integrable d lam :
    Integrable 𝔔 $ gaussianPrimitiveMeasure d :=
  joint_finite_integrable _ _
    (fun h => (𝔣 gaussianPrimitiveScalar_measurable).comp $ measurable_id.prodMk measurable_const )
    𝔣 gaussianPrimitiveScalar_slice_integrable

𝗇 𝔖 𝙷₁
theorem gaussianPrimitiveScalar_abs_integral d lam :
     ∫ e, |𝔔 e| ∂gaussianPrimitiveMeasure d ≤
      8 * |lam| * 𝔖 := by
  have hs h :
       ∫ Z, |𝔔 (Z, h)| ∂standardGaussianPi d ≤ |lam| := by
    change ∫ Z, |𝔘 * 𝔥 gaussianHermite Z| ∂standardGaussianPi d ≤ |lam|
    simp only [abs_mul, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left 𝔥 standardGaussian_hermite_abs_integral_le_two
      $ abs_nonneg 𝔘
    grind
  rw [gaussianPrimitiveMeasure, integral_prod_symm _ (𝔣 gaussianPrimitiveScalar_integrable).abs,
    integral_count]
  convert 𝗣₁ fun h _ => hs h using 1 <;> simp <;> ring

abbrev GaussianTensorMark (κ : Type*) (d : ℕ) := κ → GaussianPrimitiveMark d

𝗇 𝔇 GaussianTensorMark κ d
def gaussianTensorMeasure (κ : Type*) [Fintype κ] (d : ℕ) : Measure 𝔇 :=
  Measure.pi fun _ => gaussianPrimitiveMeasure d

def gaussianTensorScalar [Fintype κ] (lam : ℝ) (e : 𝔇) : ℝ :=
  ∏ i, 𝔔 (e i)

𝗇 𝔈 (e i).2
𝗇 𝔐 fun i => (𝔈).1.1
𝗇 𝔑 fun i => (𝔈).2.1.1
def gaussianTensorLeftPolynomial [Fintype κ] (e : 𝔇) :
    𝙣 :=
  gaussianPolynomialProduct 𝔐 𝔑

𝗇 𝔒 fun i => (𝔈).1.2
𝗇 𝔓 fun i => (𝔈).2.1.2
def gaussianTensorRightPolynomial [Fintype κ] (e : 𝔇) :
    𝙣 :=
  gaussianPolynomialProduct 𝔒 𝔓

𝗇 𝔏 gaussianTensorScalar lam e
𝗇 𝔗 𝙮
def gaussianTensorFrameAmplitude [Fintype κ] (lam : ℝ)
    (e : 𝔇) (β β' : 𝔗) : ℝ :=
  𝔏 * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'

𝗇 𝔉 gaussianTensorMeasure κ d
theorem gaussianTensorMeasure_finite κ [Fintype κ] d :
    IsFiniteMeasure 𝔉 := by
  unfold gaussianTensorMeasure
  infer_instance

𝗇 𝔎 gaussianTensorScalar (κ := κ) (d := d) lam
theorem gaussianTensorScalar_measurable [Fintype κ] (lam : ℝ) :
    Measurable 𝔎 :=
  Finset.measurable_fun_prod _ fun i _ =>
    (𝔣 gaussianPrimitiveScalar_measurable).comp $ measurable_pi_apply i

theorem gaussianTensorScalar_integrable [Fintype κ] (lam : ℝ) :
    Integrable 𝔎 𝔉 :=
  Integrable.fintype_prod fun _ => 𝔣 gaussianPrimitiveScalar_integrable

theorem gaussianTensorScalar_abs_integral [Fintype κ] (lam : ℝ) :
     ∫ e, |𝔏| ∂ 𝔉 ≤
      (8 * |lam| * 𝔖) ^ Fintype.card κ := by
  unfold gaussianTensorScalar gaussianTensorMeasure
  simp only [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod fun _ e => |𝔔 e| ]
  calc
    _ ≤ ∏ _i : κ, 8 * |lam| * 𝔖 := Finset.prod_le_prod₀
      (fun _ _ => integral_nonneg 𝗔₁)
       fun _ _ => 𝔣 gaussianPrimitiveScalar_abs_integral
    𝘿 := 𝖢₄

𝗃 𝔠 fun i => ἀ $ h i
𝗃 𝔦 fun i => ἀ 𝔈
theorem gaussianTensorPolynomial_coeff_measurable [Fintype κ]
    (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) β :
    Measurable fun e : 𝔇 =>
      (gaussianPolynomialProduct 𝔦 a 𝔦 s).coeff β := by
  have hf : Measurable fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct 𝔠 a 𝔠 s).coeff β := measurable_of_countable _
  exact hf.comp $ measurable_pi_iff.mpr fun i => measurable_snd.comp $ measurable_pi_apply i

𝗃 𝔞 fun h => ἀ
𝗃 𝔟 fun e : 𝔇 => ἀ lam e β β'
theorem gaussianTensorFrameAmplitude_measurable [Fintype κ] (lam : ℝ)
    (β β' : 𝔗) :
    Measurable 𝔟 gaussianTensorFrameAmplitude := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ)
    𝔞 h.1.1 𝔞 h.2.1.1 $ polynomialBoxExponent β.val
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ)
    𝔞 h.1.2 𝔞 h.2.1.2 $ polynomialBoxExponent β'.val
  exact ((gaussianTensorScalar_measurable lam).mul hl).mul hr

𝗇 𝔍 2 * Fintype.card κ
theorem gaussianTensorFrameAmplitude_cost_bound [Fintype κ] (lam : ℝ)
    (e : 𝔇) :
    separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e ≤
      |𝔏| * 8 ^ 𝔍 := by
  have h := gaussianPolynomialProduct_rankone_cost (D := D)
    𝔐 𝔑
    𝔒 𝔓 𝔏
  simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
    gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using h

𝗇 𝔄 gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam
theorem gaussianTensorFrameAmplitude_cost_measurable [Fintype κ] (lam : ℝ) :
    Measurable $ separatedMatrixCost 𝔄 := Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
     fun β' _ => (gaussianTensorFrameAmplitude_measurable lam β β').abs

𝗇 𝔊 Finset.sum_nonneg 𝗺₂
𝗇 𝔙 8 ^ 𝔍
theorem gaussianTensorFrameAmplitude_cost_integrable [Fintype κ] (lam : ℝ) :
    Integrable (separatedMatrixCost 𝔄)
      𝔉 := by
  apply ((gaussianTensorScalar_integrable lam).abs.mul_const
    𝔙).mono'
    (gaussianTensorFrameAmplitude_cost_measurable lam).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg 𝔊]
  exact gaussianTensorFrameAmplitude_cost_bound lam e

theorem gaussianTensorFrameAmplitude_integrated_cost [Fintype κ] (lam : ℝ) :
     ∫ e, separatedMatrixCost 𝔄 e
      ∂ 𝔉 ≤ (512 * |lam| * 𝔖) ^ Fintype.card κ := by
  have hm := integral_mono (gaussianTensorFrameAmplitude_cost_integrable (D := D) lam)
    ((gaussianTensorScalar_integrable (d := d) lam).abs.mul_const 𝔙)
    $ gaussianTensorFrameAmplitude_cost_bound lam
  rw [integral_mul_const] at hm
  have h := mul_le_mul_of_nonneg_right (gaussianTensorScalar_abs_integral (κ := κ) (d := d) lam)
    (by positivity : 0 ≤ (8 : ℝ) ^ 𝔍)
  apply hm.trans
  apply h.trans_eq
  rw [pow_mul, ← mul_pow]
  ring

def gaussianTensorAmplitude [Fintype κ] (lam : ℝ)
    (e : 𝔇) (β β' : 𝖨₁) : ℝ :=
  𝔏 * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'

𝗃 𝔤 ἀ lam (t i) $ e i
def gaussianTensorObservable [Fintype κ] (lam : ℝ) (t : 𝖱₁)
    (x y : κ → Covariate d) (e : 𝔇) : ℝ :=
  ∏ i, 𝔤 gaussianPrimitiveLeft (x i) * 𝔤 gaussianPrimitiveRight (y i)

def realMatrixSymmetrize (A : I → 𝗦₂) (i j : I) : ℝ := (𝘩 + A j i) / 2

𝗇 𝔚 A e j i
theorem separatedMatrixCost_symmetrize_le [Fintype I] [DecidableEq I]
    (A : E → I → 𝗦₂) e :
    separatedMatrixCost (fun e => realMatrixSymmetrize $ A e ) e ≤ separatedMatrixCost A e := by
  have hp i j : |realMatrixSymmetrize (A e) i j| ≤ (|A e i j| + |𝔚|) / 2 := by
    unfold realMatrixSymmetrize
    grind
  calc
    _ ≤ ∑ i : I, ∑ j : I, (|A e i j| + |𝔚|) / 2 := Finset.sum_le_sum
       fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = separatedMatrixCost A e := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => |𝔚|)]
      unfold separatedMatrixCost
      ring

def gaussianTensorSymmetricAmplitude [Fintype κ] (lam : ℝ)
    (e : 𝔇) : 𝔗 → 𝔗 → ℝ :=
  realMatrixSymmetrize $ gaussianTensorFrameAmplitude lam e

section

variable [Fintype κ]
    (lam : ℝ)

include lam

theorem gaussianTensorSymmetricAmplitude_measurable (β β' : 𝔗) :
    Measurable 𝔟 gaussianTensorSymmetricAmplitude :=
  ((gaussianTensorFrameAmplitude_measurable lam β β').add
    $ gaussianTensorFrameAmplitude_measurable lam β' β ).div_const 2

𝗇 𝔅 gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam
theorem gaussianTensorSymmetricAmplitude_cost_integrable :
    Integrable (separatedMatrixCost 𝔅)
      𝔉 := by
  have hm : Measurable $ separatedMatrixCost 𝔅 :=
    Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
       fun β' _ => (gaussianTensorSymmetricAmplitude_measurable lam β β').abs
  apply (gaussianTensorFrameAmplitude_cost_integrable lam).mono'
    hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg 𝔊]
  exact separatedMatrixCost_symmetrize_le _ e

theorem gaussianTensorSymmetricAmplitude_integrated_cost :
     ∫ e, separatedMatrixCost 𝔅 e
      ∂ 𝔉 ≤ (512 * |lam| * 𝔖) ^ Fintype.card κ :=
  (integral_mono (gaussianTensorSymmetricAmplitude_cost_integrable lam)
    (gaussianTensorFrameAmplitude_cost_integrable lam)
    $ separatedMatrixCost_symmetrize_le _ ).trans $ gaussianTensorFrameAmplitude_integrated_cost lam
