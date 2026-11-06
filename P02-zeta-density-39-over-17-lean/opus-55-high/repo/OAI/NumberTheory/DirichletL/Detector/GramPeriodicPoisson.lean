module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
public import OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson

export OAI.ProbeGramLatticeDecay (Joint)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x, y)

def embeddingPair (m : ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Joint :=
  point (ConcreteTraceCRT.eisEmbedding m.1) (ConcreteTraceCRT.eisEmbedding m.2)

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

def leftInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inl ℝ ℂ ℂ)).toContinuousLinearMap

def rightInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inr ℝ ℂ ℂ)).toContinuousLinearMap

@[simp] theorem point_eq_add (x y : ℂ) :
    point x y = leftInjection x + rightInjection y := by
  change WithLp.toLp 2 (x,y) = WithLp.toLp 2 (x,0) + WithLp.toLp 2 (0,y)
  rw [← WithLp.toLp_add]
  simp

theorem slice_isometry (y : ℂ) : Isometry (fun x : ℂ => point x y) := by
  pm_7045 x add_sub_add_right_eq_sub WithLp.norm_toLp_fst

theorem slice_temperate (y : ℂ) :
    (fun x : ℂ => point x y).HasTemperateGrowth := by
  simp only [point_eq_add]
  fun_prop

def leftSlice (W : 𝓢(Joint, ℂ)) (y : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (slice_temperate y)
    (slice_isometry y).antilipschitzWith W

@[simp] theorem leftSlice_apply (W : 𝓢(Joint, ℂ)) (y x : ℂ) :
    leftSlice W y x = W (point x y) := rfl

theorem fourier_joint_eq_iterated (f : Joint → ℂ) (hf : Integrable f) (ξ η : ℂ) :
    𝓕 f (point ξ η) =
      𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => f (point x y)) η) ξ := by
  let w : Joint := point ξ η
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z w) • f z
  pm_7737
  pm_944
  calc
    𝓕 f (point ξ η) = ∫ z : Joint, G z := rfl
    _ = ∫ z : ℂ × ℂ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℂ ℂ).integral_comp
        (MeasurableEquiv.toLp 2 (ℂ × ℂ)).measurableEmbedding G).symm
    _ = ∫ x : ℂ, ∫ y : ℂ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = _ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [G, w, point, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def partialFourier (W : 𝓢(Joint, ℂ)) (η x : ℂ) : ℂ :=
  𝓕 (fun y : ℂ => W (point x y)) η

def planeMajorant (y : ℂ) : ℝ := ((1 + ‖y‖ ^ 2) ^ 2)⁻¹

theorem planeMajorant_integrable : Integrable planeMajorant := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
    (r := 4) (by norm_num)
  change Integrable (fun y : ℂ => ((1 + ‖y‖ ^ 2) ^ 2)⁻¹)
  convert h using 1
  funext y
  rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

def majorantConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 W + 2 * SchwartzMap.seminorm ℝ 2 0 W +
    SchwartzMap.seminorm ℝ 4 0 W

section
variable (W : 𝓢(Joint, ℂ))
include W
theorem norm_le_planeMajorant (x y : ℂ) :
    ‖W (point x y)‖ ≤ majorantConstant W * planeMajorant y := by
  pm_7345 W point
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 4 (point x y)
  have hy : ‖y‖^2 ≤ ‖point x y‖^2 := by rw [norm_point_sq]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hy4 : ‖y‖^4 ≤ ‖point x y‖^4 := by nlinarith [sq_nonneg (‖x‖^2)]
  pm_7870 hm2 hy W point
  pm_7870 hm4 hy4 W point
  rw [planeMajorant, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  dsimp [majorantConstant]
  nlinarith

theorem partialFourier_continuous (η : ℂ) :
    Continuous (partialFourier W η) := by
  pm_5299 Continuous
  apply continuous_of_dominated (bound := fun y => majorantConstant W * planeMajorant y)
  · intro x
    exact ((by fun_prop : Continuous (fun y : ℂ => Real.fourierChar (-inner ℝ y η))).smul
      (W.continuous.comp (show Continuous (fun y : ℂ => point x y) from by
        simp only [point_eq_add]; fun_prop))).aestronglyMeasurable
  pm_5955 norm_le_planeMajorant W
  · exact planeMajorant_integrable.const_mul _
  · exact Eventually.of_forall fun y =>
      continuous_const.smul (W.continuous.comp (slice_isometry y).continuous)

theorem partialFourier_integrable (η : ℂ) :
    Integrable (partialFourier W η) := by
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z.snd η) • W z
  have hG : Integrable G := W.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      pm_316 G Circle.smul_def smul_eq_mul norm_mul Circle.norm_coe one_mul
      exact le_rfl)
  pm_944
  pm_5299 Integrable
  exact hGp.integral_prod_left
end

def partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (η : ℂ) : 𝓢(ℂ, ℂ) :=
  𝓕⁻ (leftSlice (𝓕 W) η)

section
variable (W : 𝓢(Joint, ℂ))
include W
theorem partialFourierSchwartz_apply (η x : ℂ) :
    partialFourierSchwartz W η x = partialFourier W η x := by
  have heq : 𝓕 (partialFourier W η) = (leftSlice (𝓕 W) η : ℂ → ℂ) := by
    funext ξ
    change 𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => W (point x y)) η) ξ = _
    rw [← fourier_joint_eq_iterated W W.integrable ξ η]
    exact (congrFun (SchwartzMap.fourier_coe W) (point ξ η)).symm
  pc_517 W leftSlice

theorem fourier_partialFourierSchwartz (ξ η : ℂ) :
    𝓕 (partialFourierSchwartz W η) ξ = (𝓕 W) (point ξ η) := by
  simp [partialFourierSchwartz]
end

def productDecayConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  2 ^ (8:ℕ) * (Finset.Iic (8,0)).sup (schwartzSeminormFamily ℝ Joint ℂ) W

section
variable (W : 𝓢(Joint, ℂ)) (x y : ℂ)
include W x y
theorem product_decay :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤ productDecayConstant W := by pm_3899

theorem norm_le_product_majorant :
    ‖W (point x y)‖ ≤ productDecayConstant W * (planeMajorant x * planeMajorant y) := by
  rw [planeMajorant, planeMajorant, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using product_decay W x y
end

theorem planeMajorant_eisenstein_summable :
    Summable (fun m : ActualEisensteinCubic.O =>
      planeMajorant (ConcreteTraceCRT.eisEmbedding m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ActualEisensteinCubic.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : ActualEisensteinCubic.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding m.val‖ := norm_pos_iff.mpr
    (ConcreteTraceCRT.eisEmbedding_ne_zero hm)
  change ((1+‖ConcreteTraceCRT.eisEmbedding m.val‖^2)^2)⁻¹ ≤
    ‖ConcreteTraceCRT.eisEmbedding m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ConcreteTraceCRT.eisEmbedding m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      ‖W (embeddingPair m)‖) := by
  pm_591 planeMajorant_eisenstein_summable.mul_of_nonneg planeMajorant_eisenstein_summable
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : ActualEisensteinCubic.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  pm_6343 mul_le_mul_of_nonneg_right hB

open scoped LineDeriv

theorem leftSlice_lineDeriv (F : 𝓢(Joint, ℂ)) (η v : ℂ) :
    ∂_{v} (leftSlice F η) = leftSlice (∂_{leftInjection v} F) η := by
  pm_8758 leftSlice_apply
  have hd : HasFDerivAt (fun x : ℂ => point x η) leftInjection x := by
    simp only [point_eq_add]
    exact leftInjection.hasFDerivAt.add_const _
  have hc := (F.hasFDerivAt (point x η)).comp x hd
  change fderiv ℝ ((F : Joint → ℂ) ∘ (fun y => point y η)) x v = _
  rw [hc.fderiv]
  rfl

section
variable (g : 𝓢(ℂ, ℂ))
include g
theorem norm_inverse_lineDeriv (v x : ℂ) :
    ‖(𝓕⁻ (∂_{v} g)) x‖ = (2 * Real.pi) * |inner ℝ x v| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℂ => inner ℝ u v).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul]
  rw [hc]
  simp only [Real.norm_eq_abs, mul_assoc]

theorem inner_sq_mul_norm_inverse_le (v x : ℂ) :
    (inner ℝ x v)^2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{v} (∂_{v} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((2 * Real.pi)^2 * (inner ℝ x v)^2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hp) (norm_nonneg _)
    _ = _ := by rw [← sq_abs (inner ℝ x v)]; ring

theorem norm_sq_mul_norm_inverse_le (x : ℂ) :
    ‖x‖^2 * ‖(𝓕⁻ g) x‖ ≤
      ‖(𝓕⁻ (∂_{(1:ℂ)} (∂_{(1:ℂ)} g))) x‖ +
      ‖(𝓕⁻ (∂_{Complex.I} (∂_{Complex.I} g))) x‖ := by
  have h1 := inner_sq_mul_norm_inverse_le g 1 x
  have hi := inner_sq_mul_norm_inverse_le g Complex.I x
  have he : (inner ℝ x (1:ℂ))^2 + (inner ℝ x Complex.I)^2 = ‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.inner, Complex.normSq_apply, sq]
  rw [← he, add_mul]
  exact add_le_add h1 hi
end

theorem norm_inverse_leftSlice_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      productDecayConstant F * planeMajorant η * ∫ y : ℂ, planeMajorant y := by
  have hb : Integrable (fun y : ℂ =>
      productDecayConstant F * planeMajorant η * planeMajorant y) :=
    planeMajorant_integrable.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun y : ℂ => Real.fourierChar (inner ℝ y x) • leftSlice F η y) hb
    (Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
        leftSlice_apply, mul_left_comm, mul_assoc, mul_comm] using norm_le_product_majorant F y η)
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice F η)) x, Real.fourierInv_eq]
  simpa only [integral_const_mul] using h

def leftSecondReal (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection (1:ℂ)} (∂_{leftInjection (1:ℂ)} F)

def leftSecondImag (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection Complex.I} (∂_{leftInjection Complex.I} F)

def sliceIntegralBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  productDecayConstant F * ∫ y : ℂ, planeMajorant y

def firstDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  sliceIntegralBound F + sliceIntegralBound (leftSecondReal F) +
    sliceIntegralBound (leftSecondImag F)

def secondDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  firstDecayBound F + firstDecayBound (leftSecondReal F) +
    firstDecayBound (leftSecondImag F)

section
variable (F : 𝓢(Joint, ℂ)) (η x : ℂ)
include F η x
theorem inverse_leftSlice_weight_le :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      ‖(𝓕⁻ (leftSlice F η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ := by
  have h := norm_sq_mul_norm_inverse_le (leftSlice F η) x
  simp only [leftSlice_lineDeriv] at h
  change ‖x‖^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
    ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
    ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ at h
  nlinarith

theorem inverse_leftSlice_first_decay :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ firstDecayBound F * planeMajorant η := by
  apply (inverse_leftSlice_weight_le F η x).trans
  pm_5585 norm_inverse_leftSlice_le
  dsimp [firstDecayBound, sliceIntegralBound]
  nlinarith

theorem inverse_leftSlice_second_decay :
    (1+‖x‖^2)^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ secondDecayBound F * planeMajorant η := by
  have h := mul_le_mul_of_nonneg_left (inverse_leftSlice_weight_le F η x)
    (show 0 ≤ 1+‖x‖^2 by positivity)
  pm_5585 inverse_leftSlice_first_decay
  dsimp [secondDecayBound]
  nlinarith
end

theorem norm_partialFourier_le (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖partialFourier W η x‖ ≤
      secondDecayBound (𝓕 W) * (planeMajorant x * planeMajorant η) := by
  rw [← partialFourierSchwartz_apply]
  change ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤ _
  have h := inverse_leftSlice_second_decay (𝓕 W) η x
  have hd : ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤
      secondDecayBound (𝓕 W) * planeMajorant η / (1+‖x‖^2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
  convert hd using 1
  simp only [planeMajorant, div_eq_mul_inv]
  ring

open EisensteinSchwartzPoisson hiding O

theorem planeMajorant_cartesian_summable :
    Summable (fun p : ℤ × ℤ => planeMajorant (complexPoint (p.1:ℝ) (p.2:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    summable_int_cauchy_product
  intro p
  change ((1+‖complexPoint (p.1:ℝ) (p.2:ℝ)‖^2)^2)⁻¹ ≤ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [Complex.sq_norm]
  simp only [complexPoint, Complex.normSq_apply]
  nlinarith [sq_nonneg (p.1:ℝ), sq_nonneg (p.2:ℝ),
    mul_nonneg (sq_nonneg (p.1:ℝ)) (sq_nonneg (p.2:ℝ))]

def cartesianPoint (p : ℤ × ℤ) : ℂ := complexPoint (p.1:ℝ) (p.2:ℝ)

section
variable (W : 𝓢(Joint, ℂ))
include W
theorem joint_cartesian_summable_norm :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  pm_591 planeMajorant_cartesian_summable.mul_of_nonneg planeMajorant_cartesian_summable
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  pm_591 planeMajorant_cartesian_summable.mul_of_nonneg planeMajorant_cartesian_summable
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))
end

theorem rightSlice_isometry (x : ℂ) : Isometry (fun y : ℂ => point x y) := by
  pm_7045 y add_sub_add_left_eq_sub WithLp.norm_toLp_snd

def rightSlice (W : 𝓢(Joint, ℂ)) (x : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by simp only [point_eq_add]; fun_prop : (fun y : ℂ => point x y).HasTemperateGrowth)
    (rightSlice_isometry x).antilipschitzWith W

section
variable (W : 𝓢(Joint, ℂ))
include W
@[simp] theorem rightSlice_apply (x y : ℂ) :
    rightSlice W x y = W (point x y) := rfl

theorem rightSlice_poisson (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  pm_383 rightSlice_apply SchwartzMap.fourier_coe hcoe partialFourier cartesianPoint h

private theorem joint_cartesian_eq_partial :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)
end

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

section
variable (W : 𝓢(Joint, ℂ))
include W
private theorem partial_cartesian_eq_fourier :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)
end

def blockMap (A : ℂ ≃L[ℝ] ℂ) : Joint ≃L[ℝ] Joint :=
  ((A.toLinearEquiv.prodCongr A.toLinearEquiv).withLpCongr 2).toContinuousLinearEquiv

section
variable (A : ℂ ≃L[ℝ] ℂ)
include A
@[simp] theorem blockMap_apply (z : Joint) :
    blockMap A z = point (A z.fst) (A z.snd) := rfl

theorem blockMap_det :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert h using 1 <;> first | rfl | ring
end

def jointInverseJacobian (A : Joint ≃L[ℝ] Joint) : ℝ :=
  |(LinearMap.det (A : Joint →ₗ[ℝ] Joint))⁻¹|

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

def jointDual (A : Joint ≃L[ℝ] Joint) : Joint →L[ℝ] Joint :=
  A.symm.toContinuousLinearMap.adjoint

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

section
variable (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ)
include A f
theorem joint_integral_comp_linearEquiv :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂ Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      pm_8219 Eventually.of_forall joint_inner_linear_dual
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl
end

def jointTranslate (W : 𝓢(Joint, ℂ)) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : Joint => z+b)
    (by fun_prop) (isometry_add_right b).antilipschitzWith W

def jointAffine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (jointTranslate W b)

section
variable (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint)
include W A
@[simp] theorem jointAffine_apply (b z : Joint) :
    jointAffine W A b z = W (A z+b) := rfl

theorem joint_fourier_affine (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]

theorem joint_affine_poisson (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  pm_8495 jointAffine_apply joint_fourier_affine
end

def jointFrequency (c : ℂ) (hc : c ≠ 0) (p : (ℤ × ℤ) × (ℤ × ℤ)) : Joint :=
  point (eisensteinDualFrequency c hc p.1) (eisensteinDualFrequency c hc p.2)

open ActualEisensteinCubic ConcreteTraceCRT

section
variable (W : 𝓢(Joint, ℂ))
include W
theorem actual_joint_coset_poisson (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*latticeCoordEquiv.symm p.1,b.2+c*latticeCoordEquiv.symm p.2)) :=
      ((latticeCoordEquiv.symm.prodCongr latticeCoordEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (eisEmbedding (b.1+c*ActualEisensteinCoordinates.eval p.1.1 p.1.2))
        (eisEmbedding (b.2+c*ActualEisensteinCoordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.2]
      change point (eisEmbedding b.1 + A (cartesianPoint p.1))
        (eisEmbedding b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+eisEmbedding b.1)
            (A (cartesianPoint p.2)+eisEmbedding b.2)
      simp only [add_comm]
    _ = _ := h

theorem joint_dual_summable_norm (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  pm_6338 hs hs.mul_left jointInverseJacobian

theorem jointFrequency_summable_norm (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  pm_99 jointDual_blockMap jointFrequency eisensteinDualFrequency cartesianPoint h
end

abbrev Residue (c : O) := O ⧸ Ideal.span {c}

def quotientPair (c : O) (m : O × O) : Residue c × Residue c :=
  (Ideal.Quotient.mk (Ideal.span {c}) m.1, Ideal.Quotient.mk (Ideal.span {c}) m.2)

def representativePair (c : O) (r : Residue c × Residue c) : O × O :=
  (GaussianShiftedPartition.representative c r.1, GaussianShiftedPartition.representative c r.2)

def jointFiberSplit (c : O) (r : Residue c × Residue c) :
    (quotientPair c ⁻¹' {r}) ≃
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.1}) ×
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.2}) where
  toFun z := (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1,z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem joint_fiber_tsum (c : O) (hc : c ≠ 0) (r : Residue c × Residue c)
    (W : O × O → ℂ) :
    (∑' m : quotientPair c ⁻¹' {r}, W m.1) =
      ∑' m : O × O, W ((representativePair c r).1+c*m.1,
        (representativePair c r).2+c*m.2) := by
  let e1 := GaussianFiberEquiv.fiberEquiv c hc r.1
    (GaussianShiftedPartition.representative c r.1)
    (GaussianShiftedPartition.representative_spec c r.1)
  let e2 := GaussianFiberEquiv.fiberEquiv c hc r.2
    (GaussianShiftedPartition.representative c r.2)
    (GaussianShiftedPartition.representative_spec c r.2)
  let e := (e1.prodCongr e2).trans (jointFiberSplit c r).symm
  exact (e.tsum_eq (fun m => W m.1)).symm

def residueFourier (c : O) (hc : c ≠ 0) (a : Residue c × Residue c → ℂ)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  ∑' r : Residue c × Residue c, a r *
    (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
      (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)

section
variable (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0) (a : Residue c × Residue c → ℂ)
include W c hc a
theorem actual_joint_periodic_poisson :
    letI : Finite (Residue c) := finite_quotient_span hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  pm_3869
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  pm_3869
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)
  pm_717
  pm_204 residueFourier tsum_fintype Circle.smul_def smul_eq_mul Finset.sum_mul mul_assoc
end

@[simp] theorem jointFrequency_zero (c : ℂ) (hc : c ≠ 0) :
    jointFrequency c hc 0 = 0 := by
  have h : complexPoint (0:ℝ) 0 = 0 := by apply Complex.ext <;> rfl
  simp [jointFrequency, eisensteinDualFrequency, h, point]

section
variable (c : O) (hc : c ≠ 0)
include c hc
@[simp] theorem residueFourier_zero
    (a : Residue c × Residue c → ℂ) :
    residueFourier c hc a 0 = ∑' r, a r := by
  simp [residueFourier]

theorem residueFourier_norm_le
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖residueFourier c hc a p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B := by
  pm_3869
  rw [residueFourier, tsum_fintype]
  calc
    _ ≤ ∑ r : Residue c × Residue c, ‖a r *
        (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
          (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Residue c × Residue c, B := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul, Circle.norm_coe, mul_one] using hB r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, Residue, pow_two]

theorem principal_joint_inverse_covolume :
    (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
      (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 = 4/3 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  pm_5670
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith
end

theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  pm_7340 q c
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖eisEmbedding c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

def scaleMap (t : ℝ) (ht : 0 < t) : Joint ≃L[ℝ] Joint :=
  blockMap (complexMulEquiv ((t⁻¹:ℝ):ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero ht.ne')))

section
variable (t : ℝ) (ht : 0 < t)
include t ht
@[simp] theorem scaleMap_apply (z : Joint) :
    scaleMap t ht z = t⁻¹ • z := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [scaleMap, blockMap_apply, complexMulEquiv_apply, point, Algebra.smul_def]

theorem scaleMap_dual (z : Joint) :
    jointDual (scaleMap t ht) z = t • z := by
  have hz : z = point z.fst z.snd := rfl
  conv_lhs => rw [hz]
  rw [scaleMap, jointDual_blockMap, dual_mul_apply, dual_mul_apply]
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [point, Algebra.smul_def]

theorem scaleMap_inverseJacobian :
    jointInverseJacobian (scaleMap t ht) = t^4 := by
  rw [scaleMap, jointInverseJacobian_blockMap, inverseJacobian, complexMulEquiv_det,
    abs_inv, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← inv_pow, inv_inv]
  ring
end

def scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) : 𝓢(Joint, ℂ) :=
  jointAffine W (scaleMap t ht) 0

section
variable (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint)
include W t ht z
@[simp] theorem scaledSource_apply :
    scaledSource W t ht z = W (t⁻¹ • z) := by
  simp [scaledSource]

theorem fourier_scaledSource :
    (𝓕 (scaledSource W t ht)) z = t^4 • (𝓕 W) (t • z) := by
  rw [scaledSource, joint_fourier_affine, scaleMap_inverseJacobian, scaleMap_dual]
  simp
end

theorem scaledSource_physicalPoint (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) (m : O × O) :
    scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN) (embeddingPair m) =
      W (ProbeGramLatticeDecay.physicalPoint N m) := by
  rw [scaledSource_apply, ProbeGramLatticeDecay.physicalPoint_eq_smul]
  rfl

def generatorRotation (c : ℂ) : ℂ := (‖c‖:ℂ) / starRingEnd ℂ c

section
variable (c : ℂ) (hc : c ≠ 0)
include c hc
theorem norm_generatorRotation : ‖generatorRotation c‖ = 1 := by
  simp [generatorRotation, Complex.norm_real, norm_ne_zero_iff.mpr hc]

theorem scaled_jointFrequency_eq (N : ℝ) (hN : 0 < N)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    Real.sqrt N • jointFrequency c hc p =
      ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/‖c‖^2)) (generatorRotation c) p := by
  pm_7308 hn c hc
  have hs : Real.sqrt (N/‖c‖^2) = Real.sqrt N / ‖c‖ := by
    rw [Real.sqrt_div hN.le, Real.sqrt_sq (norm_nonneg c)]
  have hcoord (v : ℤ × ℤ) : (Real.sqrt N:ℂ) * eisensteinDualFrequency c hc v =
      generatorRotation c * (Real.sqrt (N/‖c‖^2):ℂ) * explicitDualFrequency 1 v := by
    rw [eisensteinDualFrequency_explicit, hs]
    pm_93 generatorRotation explicitDualFrequency map_one div_one Complex.ofReal_div
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp
  apply WithLp.ofLp_injective
  change (Real.sqrt N • eisensteinDualFrequency c hc p.1,
    Real.sqrt N • eisensteinDualFrequency c hc p.2) = _
  apply Prod.ext
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.1
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.2
end

theorem sqrt_ratio_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (A : ℕ) :
    (Real.sqrt (N/q))^(-((2*A:ℕ):ℝ)) = (q/N)^A := by
  rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (div_nonneg hN.le hq.le), ← inv_pow, inv_div]

theorem physical_weighted_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    Summable (fun m : O × O => d m * W (ProbeGramLatticeDecay.physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ProbeGramLatticeDecay.physical_summable W N hN).mul_left B)
  pm_1479 hB

theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  pm_205 S C hC hhigh ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  pm_7340 q c
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring

def idealQuotientPair (r : Ideal O) (m : O × O) : (O ⧸ r) × (O ⧸ r) :=
  (Ideal.Quotient.mk r m.1, Ideal.Quotient.mk r m.2)

section
variable (A : ℕ) (hA : 2 < A) (a b : ℝ) (ha : 0 < a) (hab : a < b)
include A hA a b ha hab
theorem principal_annular_periodic_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  pm_732 Sl Cl hCl hl ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  pm_205 Sh Ch hCh hh principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

theorem ideal_annular_periodic_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  pm_562 S C hC h principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W hW c hc
end

end ProbeGramPeriodicPoisson

end

end OAI
