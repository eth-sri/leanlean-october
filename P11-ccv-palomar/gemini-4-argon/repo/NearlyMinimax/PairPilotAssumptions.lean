module
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import NearlyMinimax.LocalizationL2
public import NearlyMinimax.Risk
public import NearlyMinimax.PairDesignMeasure
public import NearlyMinimax.PairWindowModel
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
abbrev PairVector := EuclideanSpace ℝ (Fin 3)
def pairResponseVector (y y' : ℝ) : PairVector := WithLp.toLp 2 ![y', y, 1]
def pairCoordinateVector (i : Fin 3) : PairVector :=
  WithLp.toLp 2 (Pi.single i 1)
def pairNoiseOperator : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0) +
    InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1)
def pairScoreOperator (V y y' : ℝ) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairResponseVector y y') (pairResponseVector y y') -
    V • pairNoiseOperator
theorem pairResponseVector_norm_sq (y y' ) :
    ‖pairResponseVector y y'‖ ^ 2 = y' ^ 2 + y ^ 2 + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pairResponseVector, Fin.sum_univ_succ, add_assoc]
theorem pairCoordinateVector_norm (i ) : ‖pairCoordinateVector i‖ = 1 := by
  have : ‖pairCoordinateVector i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [pairCoordinateVector, Finset.sum_ite_eq']
  nlinarith [norm_nonneg (pairCoordinateVector i)]
theorem pairNoiseOperator_norm_le : ‖pairNoiseOperator‖ ≤ 2 := by
  have h := norm_add_le
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0))
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1))
  norm_num only [InnerProductSpace.norm_rankOne, pairCoordinateVector_norm,
    one_mul] at h
  exact h
theorem pairScoreOperator_norm_sq_le (V y y' ) :
    ‖pairScoreOperator V y y'‖ ^ 2 ≤ 6 * (y ^ 4 + y' ^ 4 + 1) + 8 * V ^ 2 := by
  have hn : ‖pairScoreOperator V y y'‖ ≤ ‖pairResponseVector y y'‖ ^ 2 + 2 * |V| := by
    apply (norm_sub_le _ _).trans
    simp only [InnerProductSpace.norm_rankOne, norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left pairNoiseOperator_norm_le (abs_nonneg V)
    nlinarith
  have := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have : ‖pairResponseVector y y'‖ ^ 4 ≤ 3 * (y ^ 4 + y' ^ 4 + 1) := by
    rw [show ‖pairResponseVector y y'‖ ^ 4 = (‖pairResponseVector y y'‖ ^ 2) ^ 2 by ring,
      pairResponseVector_norm_sq]
    nlinarith [sq_nonneg (y ^ 2 - y' ^ 2), sq_nonneg (y ^ 2 - 1),
      sq_nonneg (y' ^ 2 - 1)]
  have  := sq_abs V
  nlinarith [sq_nonneg (‖pairResponseVector y y'‖ ^ 2 - 2 * |V|)]
theorem pairResponseVector_continuous :
    Continuous (fun z : ℝ × ℝ => pairResponseVector z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [pairResponseVector] <;> fun_prop
theorem pairResponseVector_inner (a y y') :
    ⟪a, pairResponseVector y y'⟫ = a 0 * y' + a 1 * y + a 2 := by
  simp only [PiLp.inner_apply, pairResponseVector, RCLike.inner_apply,
    conj_trivial]
  simp [Fin.sum_univ_succ]
  ring
theorem pairNoiseOperator_inner (a b ) :
    ⟪a, pairNoiseOperator b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp only [pairNoiseOperator, ContinuousLinearMap.add_apply, inner_add_right,
    InnerProductSpace.inner_right_rankOne_apply]
  simp [pairCoordinateVector, PiLp.inner_apply, RCLike.inner_apply]
theorem pairScoreOperator_inner_polynomial (V y y' a b) :
    ⟪a, pairScoreOperator V y y' b⟫ =
      a 0 * b 0 * y' ^ 2 + a 1 * b 1 * y ^ 2 +
      (a 0 * b 1 + a 1 * b 0) * (y * y') +
      (a 0 * b 2 + a 2 * b 0) * y' +
      (a 1 * b 2 + a 2 * b 1) * y + a 2 * b 2 -
      V * (a 0 * b 0 + a 1 * b 1) := by
  simp only [pairScoreOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner,
    pairNoiseOperator_inner]
  rw [real_inner_comm b (pairResponseVector y y'), pairResponseVector_inner]
  ring
end NearlyMinimax
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.PilotFluctuation
open MeasureTheory
open scoped RealInnerProductSpace
variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem three_square_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
end NearlyMinimax.PilotFluctuation
namespace NearlyMinimax.PilotFields
open MeasureTheory
open scoped RealInnerProductSpace
variable {C lam : ℝ} {f g v v₁ v₂ : W → H}
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]
theorem toLp_norm_sq {f : W → H} (hf : MemLp f 2 M) :
    ‖hf.toLp f‖ ^ 2 = ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with w hw
  rw [hw, real_inner_self_eq_norm_sq]
theorem inner_integral_sq_le {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    (∫ w, ⟪f w, g w⟫ ∂M) ^ 2 ≤
      (∫ w, ‖f w‖ ^ 2 ∂M) * (∫ w, ‖g w‖ ^ 2 ∂M) := by
  have h_toLp_inner : ⟪hf.toLp f, hg.toLp g⟫ = ∫ w, ⟪f w, g w⟫ ∂M := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
    rw [hfw, hgw]
  rw [← h_toLp_inner, ← toLp_norm_sq hf, ← toLp_norm_sq hg]
  calc
    _ ≤ (‖hf.toLp f‖ * ‖hg.toLp g‖) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)) 2
    _ = _ := by ring
theorem inner_integrable {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    Integrable (fun w => ⟪f w, g w⟫) M := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  rw [hfw, hgw]
def test (η : Ω → W → H) (v : W → H) (x : Ω) : ℝ :=
  ∫ w, ⟪η x w, v w⟫ ∂M
theorem memLp_sections {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M)) :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M := by
  filter_upwards [hη.aestronglyMeasurable.prodMk_left,
    hη.norm.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi
theorem test_aestronglyMeasurable 
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    AEStronglyMeasurable (test (M := M) η v) μ := by
  have hm : AEStronglyMeasurable
      (fun z => ⟪η z.1 z.2, v z.2⟫) (μ.prod M) :=
    hη.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd
  exact hm.integral_prod_right'
theorem test_sq_integrable 
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    Integrable (fun x => test (M := M) η v x ^ 2) μ := by
  have hi := hη.norm.integrable_sq.integral_prod_left.mul_const
    (∫ w, ‖v w‖ ^ 2 ∂M)
  apply hi.mono' ((test_aestronglyMeasurable hη hv).pow 2)
  filter_upwards [memLp_sections hη] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact inner_integral_sq_le hx hv
theorem test_memLp_two 
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    MemLp (test (M := M) η v) 2 μ :=
  (memLp_two_iff_integrable_sq (test_aestronglyMeasurable hη hv)).2
    (test_sq_integrable hη hv)
theorem test_mean_zero [CompleteSpace H] {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {v : W → H} (hv : MemLp v 2 M) :
    (∫ x, test (M := M) η v x ∂μ) = 0 := by
  have hcomp : MemLp (fun z : Ω × W => v z.2) 2 (μ.prod M) :=
    hv.comp_measurePreserving measurePreserving_snd
  have hi := inner_integrable hη hcomp
  change (∫ x, ∫ w, ⟪η x w, v w⟫ ∂M ∂μ) = 0
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hcenter, hη.aestronglyMeasurable.prodMk_right,
    hη.norm.integrable_sq.prod_left_ae] with w hw hm hisq
  calc
    (∫ x, ⟪η x w, v w⟫ ∂μ) = ∫ x, ⟪v w, η x w⟫ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => real_inner_comm _ _)
    _ = ⟪v w, ∫ x, η x w ∂μ⟫ := integral_inner (((memLp_two_iff_integrable_sq_norm hm).2 hisq).integrable (by norm_num)) _
    _ = 0 := by rw [hw]; simp
section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M
theorem bilinear_measurable 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hmB : Measurable (fun z : W × H => B z.1 z.2)) :
    Measurable (bilinear (M := M) η B) := by
  have hm : Measurable (fun z : (Ω × Ω) × W =>
      ⟪η z.1.1 z.2, B z.2 (η z.1.2 z.2)⟫) := by
    apply Measurable.inner
    · exact hmη.comp (measurable_fst.fst.prodMk measurable_snd)
    · exact hmB.comp (measurable_snd.prodMk
        (hmη.comp (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
theorem operatorField_memLp {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) :
    MemLp (fun w => B w (f w)) 2 M := by
  apply hf.of_le_mul (c := C)
    (hmB.comp (measurable_id.prodMk hmf)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w =>
    ((B w).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _)))
theorem operatorField_energy_le {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hC : 0 ≤ C) (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) :
    (∫ w, ‖B w (f w)‖ ^ 2 ∂M) ≤ C ^ 2 * ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← integral_const_mul]
  apply integral_mono (operatorField_memLp hmB hbound hmf hf).norm.integrable_sq
    (hf.norm.integrable_sq.const_mul (C ^ 2))
  intro w
  calc
    ‖B w (f w)‖ ^ 2 ≤ (C * ‖f w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (((B w).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))) 2
    _ = C ^ 2 * ‖f w‖ ^ 2 := by ring
theorem bilinear_section_energy_le 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {y : Ω} (hy : MemLp (η y) 2 M) :
    (∫ x, bilinear (M := M) η B (x, y) ^ 2 ∂μ) ≤
      lam * C ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M := by
  have hm : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hb := (htest (fun w => B w (η y w)) (operatorField_memLp hmB hbound hm hy)).trans
    (mul_le_mul_of_nonneg_left (operatorField_energy_le hmB hC hbound hm hy) hlam)
  simpa only [test, bilinear, mul_assoc] using hb
theorem bilinear_sq_integrable 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    Integrable (fun z => bilinear (M := M) η B z ^ 2) (μ.prod μ) := by
  have hmZ : AEStronglyMeasurable
      (fun z : Ω × Ω => bilinear (M := M) η B z ^ 2) (μ.prod μ) :=
    (bilinear_measurable (M := M) hmη hmB).aestronglyMeasurable.pow 2
  apply (integrable_prod_iff' hmZ).2
  constructor
  · filter_upwards [memLp_sections hη] with y hy
    exact test_sq_integrable hη (operatorField_memLp hmB hbound (hmη.comp (measurable_const.prodMk measurable_id)) hy)
  · have hi := hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C ^ 2)
    apply hi.mono' hmZ.norm.prod_swap.integral_prod_right'
    filter_upwards [memLp_sections hη] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [norm_pow, Real.norm_eq_abs, sq_abs]
    exact bilinear_section_energy_le hmη hmB hC hlam hbound htest hy
theorem bilinear_memLp_two 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    MemLp (bilinear (M := M) η B) 2 (μ.prod μ) :=
  (memLp_two_iff_integrable_sq
    (bilinear_measurable (M := M) hmη hmB).aestronglyMeasurable).2
    (bilinear_sq_integrable hmη hη hmB hC hlam hbound htest)
def fluctuation (η : Ω → W → H) (B : W → H →L[ℝ] H)
    (v₁ v₂ : W → H) (z : Ω × Ω) : ℝ :=
  test (M := M) η v₁ z.1 + test (M := M) η v₂ z.2 + bilinear (M := M) η B z
theorem fluctuation_memLp_two 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    MemLp (fluctuation (M := M) η B v₁ v₂) 2 (μ.prod μ) := (((test_memLp_two hη hv₁).comp_measurePreserving measurePreserving_fst).add ((test_memLp_two hη hv₂).comp_measurePreserving measurePreserving_snd)).add (bilinear_memLp_two hmη hη hmB hC hlam hbound htest)
theorem fluctuation_energy_le 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ^ 2 ∂μ.prod μ) ≤
      3 * lam * ((∫ w, ‖v₁ w‖ ^ 2 ∂M) + (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have h₁ := (test_sq_integrable hη hv₁).comp_fst μ
  have h₂ := (test_sq_integrable hη hv₂).comp_snd μ
  have h₃ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
  calc
    _ ≤ ∫ z : Ω × Ω, 3 * (test (M := M) η v₁ z.1 ^ 2 +
        test (M := M) η v₂ z.2 ^ 2 + bilinear (M := M) η B z ^ 2) ∂μ.prod μ := by
      exact integral_mono
        (fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hv₁ hv₂).integrable_sq
        (((h₁.add h₂).add h₃).const_mul 3)
        (fun _ => PilotFluctuation.three_square_le _ _ _)
    _ = 3 * ((∫ x, test (M := M) η v₁ x ^ 2 ∂μ) +
        (∫ x, test (M := M) η v₂ x ^ 2 ∂μ) +
        (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ)) := by
      have ha := integral_add (h₁.add h₂) h₃
      have hb := integral_add h₁ h₂
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst (μ := μ) (ν := μ) (fun x => test (M := M) η v₁ x ^ 2),
        integral_fun_snd (μ := μ) (ν := μ) (fun x => test (M := M) η v₂ x ^ 2)]
      simp
    _ ≤ 3 * (lam * (∫ w, ‖v₁ w‖ ^ 2 ∂M) + lam * (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
      gcongr
      · exact htest v₁ hv₁
      · exact htest v₂ hv₂
      have h_bilinear_energy_le : (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ) ≤
      lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M := by
        have hZ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
        rw [integral_prod_symm _ hZ]
        calc
          _ ≤ ∫ y, lam * C ^ 2 * (∫ w, ‖η y w‖ ^ 2 ∂M) ∂μ := by
            apply integral_mono_ae hZ.integral_prod_right
              (hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C ^ 2))
            filter_upwards [memLp_sections hη] with y hy
            exact bilinear_section_energy_le hmη hmB hC hlam hbound htest hy
          _ = _ := by
            rw [integral_const_mul, integral_prod _ hη.norm.integrable_sq]
      · exact h_bilinear_energy_le
    _ = _ := by ring
end OperatorField
end NearlyMinimax.PilotFields
end
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax
open MeasureTheory
open scoped ENNReal
theorem two_stage_mean_squared_bound 
    [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : P × X → ℝ) (L b : P → ℝ) (hmT : Measurable T) (hmL : Measurable L)
    (hb : Integrable b μ) (hb0 : ∀ᵐ p ∂μ, 0 ≤ b p)
    {a d c : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hconditional : ∀ᵐ p ∂μ,
      (∫⁻ x, ENNReal.ofReal ((T (p, x) - L p) ^ 2) ∂ν) ≤ ENNReal.ofReal (a * b p))
    (hmean : (∫⁻ p, ENNReal.ofReal ((L p - c) ^ 2) ∂μ) ≤ ENNReal.ofReal d) :
    (∫⁻ z, ENNReal.ofReal ((T z - c) ^ 2) ∂μ.prod ν) ≤
      ENNReal.ofReal (2 * a * (∫ p, b p ∂μ) + 2 * d) := by
  let f : P × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((T z - L z.1) ^ 2)
  let g : P × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((L z.1 - c) ^ 2)
  have hf : Measurable f := ((hmT.sub (hmL.comp measurable_fst)).pow_const 2).ennreal_ofReal
  have hg : Measurable g := (((hmL.comp measurable_fst).sub measurable_const).pow_const 2).ennreal_ofReal
  have : (∫⁻ z, f z ∂μ.prod ν) ≤ ENNReal.ofReal (a * ∫ p, b p ∂μ) := by
    rw [lintegral_prod _ hf.aemeasurable]
    apply (lintegral_mono_ae hconditional).trans
    rw [← ofReal_integral_eq_lintegral_ofReal (hb.const_mul a) (hb0.mono (fun _ hp => mul_nonneg ha hp)), integral_const_mul]
  have hmean' : (∫⁻ z, g z ∂μ.prod ν) ≤ ENNReal.ofReal d := by
    rw [lintegral_prod _ hg.aemeasurable]
    simp only [g, lintegral_const, measure_univ, mul_one]
    exact hmean
  calc
    _ ≤ ∫⁻ z, (2 : ℝ≥0∞) * f z + 2 * g z ∂μ.prod ν := by
      apply lintegral_mono
      intro z
      have hs : (T z - c) ^ 2 ≤ 2 * (T z - L z.1) ^ 2 + 2 * (L z.1 - c) ^ 2 := by
        nlinarith [sq_nonneg ((T z - L z.1) - (L z.1 - c))]
      have he := ENNReal.ofReal_le_ofReal hs
      simpa only [f, g, ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (T z - L z.1) ^ 2)
        (by positivity : 0 ≤ 2 * (L z.1 - c) ^ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using he
    _ = 2 * (∫⁻ z, f z ∂μ.prod ν) + 2 * (∫⁻ z, g z ∂μ.prod ν) := by
      have hf2 : Measurable (fun z => (2 : ℝ≥0∞) * f z) := measurable_const.mul hf
      rw [lintegral_add_left hf2, lintegral_const_mul _ hf, lintegral_const_mul _ hg]
    _ ≤ 2 * ENNReal.ofReal (a * ∫ p, b p ∂μ) + 2 * ENNReal.ofReal d := by
      gcongr
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg ha (integral_nonneg_of_ae hb0))) (mul_nonneg (by norm_num) hd)]
      congr 1
      ring
end NearlyMinimax
namespace NearlyMinimax.PairUStatistic
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
section
section
variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]
end
variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]
def weightedSymmetrization (weight : ℝ) (G : E × E → ℝ) (z : E × E) : ℝ :=
  weight / 4 * (G z + G z.swap)
theorem weightedSymmetrization_memLp (weight : ℝ) {G : E × E → ℝ}
    (hG : MemLp G 2 (μ.prod μ)) : MemLp (weightedSymmetrization weight G) 2 (μ.prod μ) :=
  (hG.add (hG.comp_measurePreserving Measure.measurePreserving_swap)).const_mul _
theorem weighted_pair_centered_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → E) (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    (label : E → I) (hlabel : Measurable label)
    {G : E × E → ℝ} (hmG : Measurable G) (hG : MemLp G 2 (μ.prod μ))
    (hsupport : ∀ x y, label x ≠ label y → G (x, y) = 0)
    {weight cap P : ℝ} (hweight : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hP : weight * cap ≤ P) :
    (∫ x, (pairAverage n (weightedSymmetrization weight G) (fun i => X i x) -
      weight / 2 * ∫ z, G z ∂μ.prod μ) ^ 2 ∂ν) ≤
      (P / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) *
        (weight * ∫ z, G z ^ 2 ∂μ.prod μ) := by
  have h_weightedSymmetrization_measurable : Measurable (weightedSymmetrization weight G) := (hmG.add (hmG.comp measurable_swap)).const_mul _
  have h_weightedSymmetrization_symmetric (x : E) (y : E) : weightedSymmetrization weight G (x, y) = weightedSymmetrization weight G (y, x) := by
    simp only [weightedSymmetrization, Prod.swap_prod_mk, add_comm]
  have h_weightedSymmetrization_supported : ∀ x y, label x ≠ label y → weightedSymmetrization weight G (x, y) = 0 := by
    intro x y hxy
    simp only [weightedSymmetrization, Prod.swap_prod_mk, hsupport x y hxy,
      hsupport y x (Ne.symm hxy), add_zero, mul_zero]
  have h_partition_pairAverage_centered_sq_le {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ)) (hsym : ∀ x y, K (x, y) = K (y, x)) (hsupport : ∀ x y, label x ≠ label y → K (x, y) = 0) : (∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν) ≤
      (4 / ↑n * cap + 2 / (↑n * (n - 1 : ℕ))) *
        ∫ z, K z ^ 2 ∂μ.prod μ := by
    apply (pairAverage_centered_sq_le hn X hind hX hmK hK hsym).trans
    have h_partition_row_energy_le : (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) ≤
        cap * ∫ z, K z ^ 2 ∂μ.prod μ := by
      have hsec : ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 μ :=
        PilotFields.memLp_sections hK
      calc
        _ ≤ ∫ x, cap * (∫ y, K (x, y) ^ 2 ∂μ) ∂μ := by
          apply integral_mono_ae (rowIntegral_sq_integrable hK)
            (hK.integrable_sq.integral_prod_left.const_mul cap)
          filter_upwards [hsec] with x hx
          let S := label ⁻¹' {label x}
          have hS : MeasurableSet S := (measurableSet_singleton _).preimage hlabel
          have he : S.indicator (fun y => K (x, y)) = (fun y => K (x, y)) := by
            funext y
            by_cases hy : y ∈ S
            · exact indicator_of_mem hy _
            · rw [indicator_of_notMem hy]
              exact (hsupport x y (by simpa only [S, mem_preimage, mem_singleton_iff, ne_comm] using hy)).symm
          have he₂ : S.indicator (fun y => K (x, y) ^ 2) = (fun y => K (x, y) ^ 2) := by
            funext y
            by_cases hy : y ∈ S
            · exact indicator_of_mem hy _
            · rw [indicator_of_notMem hy,
                hsupport x y (by simpa only [S, mem_preimage, mem_singleton_iff, ne_comm] using hy)]
              norm_num
          have hrestrict : (μ.restrict S).real univ = μ.real S := by
            simp only [Measure.real, Measure.restrict_apply_univ]
          calc
            _ = (∫ y in S, K (x, y) ∂μ) ^ 2 := by
              rw [← integral_indicator hS, he]
              rfl
            _ ≤ (μ.restrict S).real univ * ∫ y in S, K (x, y) ^ 2 ∂μ :=
              LocalizationL2.integral_sq_le_mass_mul_integral_sq (hx.restrict S)
            _ = μ.real S * ∫ y, K (x, y) ^ 2 ∂μ := by
              rw [hrestrict, ← integral_indicator hS, he₂]
            _ ≤ _ := mul_le_mul_of_nonneg_right (hmass (label x))
              (integral_nonneg (fun _ => sq_nonneg _))
        _ = _ := by rw [integral_const_mul, integral_prod _ hK.integrable_sq]
    have := mul_le_mul_of_nonneg_left
      h_partition_row_energy_le
      (by positivity : 0 ≤ 4 / (n : ℝ))
    nlinarith
  have hv := (h_partition_pairAverage_centered_sq_le h_weightedSymmetrization_measurable (weightedSymmetrization_memLp weight hG) h_weightedSymmetrization_symmetric h_weightedSymmetrization_supported)
  have h_weightedSymmetrization_mean : (∫ z, weightedSymmetrization weight G z ∂μ.prod μ) =
      weight / 2 * ∫ z, G z ∂μ.prod μ := by
    have h₁ := hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have ha := integral_add h₁ h₂
    simp only [Function.comp_def] at ha
    simp only [weightedSymmetrization]
    rw [integral_const_mul, ha, integral_prod_swap G]
    ring
  rw [h_weightedSymmetrization_mean] at hv
  apply hv.trans
  have hcoef : 0 ≤ 4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ)) := by positivity
  have h_weightedSymmetrization_energy_le : (∫ z, weightedSymmetrization weight G z ^ 2 ∂μ.prod μ) ≤
      weight ^ 2 / 4 * ∫ z, G z ^ 2 ∂μ.prod μ := by
    have h₁ := hG.integrable_sq
    have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable_sq
    calc
      _ ≤ ∫ z : E × E, weight ^ 2 / 8 * (G z ^ 2 + G z.swap ^ 2) ∂μ.prod μ := by
        apply integral_mono (weightedSymmetrization_memLp weight hG).integrable_sq
          ((h₁.add h₂).const_mul _)
        intro z
        have hs : (G z + G z.swap) ^ 2 ≤ 2 * (G z ^ 2 + G z.swap ^ 2) := by
          nlinarith [sq_nonneg (G z - G z.swap)]
        have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ weight ^ 2 / 16)
        dsimp [weightedSymmetrization]
        nlinarith
      _ = _ := by
        have ha := integral_add h₁ h₂
        simp only [Pi.add_apply, Function.comp_def] at ha
        rw [integral_const_mul, ha, integral_prod_swap (fun z => G z ^ 2)]
        ring
  apply (mul_le_mul_of_nonneg_left h_weightedSymmetrization_energy_le hcoef).trans
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm0 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have henergy : 0 ≤ ∫ z, G z ^ 2 ∂μ.prod μ := integral_nonneg (fun _ => sq_nonneg _)
  have hscale : (4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ))) * (weight ^ 2 / 4) =
      (weight * cap / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) * weight := by
    field_simp
    <;> ring
  rw [← mul_assoc, hscale]
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (div_le_div_of_nonneg_right hP hn0.le)
        (weight / (2 * (n : ℝ) * (n - 1 : ℕ)))) hweight.le) henergy
  nlinarith
end
variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
def fieldPairAverage (n ) (weight : ℝ) (G : P → E × E → ℝ)
    (X : Fin n → Ω → E) (z : P × Ω) : ℝ :=
  pairAverage n (weightedSymmetrization weight (G z.1)) (fun i => X i z.2)
theorem fieldPairAverage_measurable (n weight) 
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i)) :
    Measurable (fieldPairAverage n weight G X) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  apply Measurable.const_mul
  exact (hmG.comp (measurable_fst.prodMk
    (((hX i).comp measurable_snd).prodMk ((hX j).comp measurable_snd)))).add
      (hmG.comp (measurable_fst.prodMk
        (((hX j).comp measurable_snd).prodMk ((hX i).comp measurable_snd))))
def fieldPairMean (weight : ℝ) (G : P → E × E → ℝ) (p : P) : ℝ :=
  weight / 2 * ∫ z, G p z ∂μ.prod μ
end NearlyMinimax.PairUStatistic
end
section
section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
def boundedRegression  (C : ModelConstants d) (θ : RegressionParameter d)
    (x : Covariate d) : ℝ := clip (-C.holderBound) C.holderBound (θ.regression x)
theorem boundedRegression_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) : Measurable (boundedRegression C θ) :=
  (clip_lipschitz _ _).continuous.measurable.comp hθ.2.1
theorem boundedRegression_eq_on_cube  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) 
    (hx : x ∈ unitCube d) : boundedRegression C θ x = θ.regression x := by
  have h := abs_le.mp (admissible_regression_value_bound C θ hθ x hx)
  exact clip_target h.1 h.2
def boundedPairRegressionOperator  (C : ModelConstants d) (θ : RegressionParameter d)
    (w : Covariate d × Covariate d) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
theorem boundedPairRegressionOperator_norm_le  (C : ModelConstants d)
    (θ w) :
    ‖boundedPairRegressionOperator C θ w‖ ≤ 2 * C.holderBound ^ 2 + 1 := by
  have h_boundedRegression_abs_le (x) : |boundedRegression C θ x| ≤ C.holderBound := by
    have h := clip_mem_Icc (x := θ.regression x)
      (show -C.holderBound ≤ C.holderBound by linarith [C.holderBound_pos])
    exact abs_le.2 h
  rw [boundedPairRegressionOperator, InnerProductSpace.norm_rankOne, ← pow_two,
    pairResponseVector_norm_sq]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (h_boundedRegression_abs_le w.1) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (h_boundedRegression_abs_le w.2) 2
  simp only [sq_abs] at h1 h2
  linarith
theorem boundedPairRegressionOperator_symmetric {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (w : Covariate d × Covariate d) (a b : PairVector) :
    ⟪a, boundedPairRegressionOperator C θ w b⟫ = ⟪boundedPairRegressionOperator C θ w a, b⟫ := by
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_smul_left, real_inner_comm, starRingEnd_apply, star_trivial]
  ring
theorem boundedPairRegressionOperator_measurable_apply  (C θ) (hθ : Admissible C θ) :
    Measurable (fun z : (Covariate d × Covariate d) × PairVector =>
      boundedPairRegressionOperator C θ z.1 z.2) := by
  have hv  :=
    pairResponseVector_continuous.measurable.comp
      (((boundedRegression_measurable C θ hθ).comp measurable_fst).prodMk
        ((boundedRegression_measurable C θ hθ).comp measurable_snd))
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply]
  have hi : Measurable (fun z : (Covariate d × Covariate d) × PairVector =>
      ⟪pairResponseVector (boundedRegression C θ z.1.1) (boundedRegression C θ z.1.2), z.2⟫) :=
    (hv.comp measurable_fst).inner measurable_snd
  have hs : Continuous (fun z : ℝ × PairVector => z.1 • z.2) :=
    continuous_fst.smul continuous_snd
  exact hs.measurable.comp (hi.prodMk (hv.comp measurable_fst))
theorem regularPairDesignMeasure_cube_ae  (C θ) (hθ : Admissible C θ)
    (k hk) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
  let := designLaw_isProbability C θ hθ
  apply (Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict).ae_le
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ),
    (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hy
  exact ⟨hx, hy⟩
theorem boundedPairRegressionOperator_eq_ae  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk) :
    boundedPairRegressionOperator C θ =ᵐ[regularPairDesignMeasure θ k hk]
      (fun w => InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))) := by
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ k hk] with w hw
  simp only [boundedPairRegressionOperator, boundedRegression_eq_on_cube C θ hθ hw.1,
    boundedRegression_eq_on_cube C θ hθ hw.2]
end NearlyMinimax
end
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.PilotFields
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
section
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]
def pilotMean (m : W → H) (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪m w + η z.1 w, B w (m w + η z.2 w)⟫ ∂M
theorem pilotMean_sub_eq (m ) (hmm : Measurable m) (hm : MemLp m 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    {x y : Ω} (hx : MemLp (η x) 2 M) (hy : MemLp (η y) 2 M) :
    pilotMean (M := M) m η B (x, y) - (∫ w, ⟪m w, B w (m w)⟫ ∂M) =
      fluctuation (M := M) η B (fun w => B w (m w)) (fun w => B w (m w)) (x, y) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hBy := operatorField_memLp hmB hbound hmy hy
  have h₀ := inner_integrable hm hBm
  have h₁ := inner_integrable hx hBm
  have h₂ := inner_integrable hy hBm
  have h₃ := inner_integrable hx hBy
  have he : (fun w => ⟪m w + η x w, B w (m w + η y w)⟫) =
      (fun w => ⟪m w, B w (m w)⟫ + ⟪η x w, B w (m w)⟫ +
        ⟪η y w, B w (m w)⟫ + ⟪η x w, B w (η y w)⟫) := by
    funext w
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      hsym w (m w) (η y w), real_inner_comm (B w (m w)) (η y w)]
    ring
  have ha := integral_add ((h₀.add h₁).add h₂) h₃
  have hb := integral_add (h₀.add h₁) h₂
  have hc := integral_add h₀ h₁
  simp only [Pi.add_apply] at ha hb hc
  simp only [pilotMean, fluctuation, test, bilinear]
  rw [he, ha, hb, hc]
  ring
theorem pilotMean_centered_sq_le (m ) (hmm : Measurable m) (hm : MemLp m 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, (pilotMean (M := M) m η B z - ∫ w, ⟪m w, B w (m w)⟫ ∂M) ^ 2 ∂μ.prod μ) ≤
      3 * lam * C ^ 2 * (2 * (∫ w, ‖m w‖ ^ 2 ∂M) +
        ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have he : (fun z => (pilotMean (M := M) m η B z - ∫ w, ⟪m w, B w (m w)⟫ ∂M) ^ 2) =ᵐ[μ.prod μ]
      (fun z => fluctuation (M := M) η B (fun w => B w (m w))
        (fun w => B w (m w)) z ^ 2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (memLp_sections hη),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (memLp_sections hη)] with z hx hy
    rw [pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy]
  rw [integral_congr_ae he]
  apply (fluctuation_energy_le hmη hη hmB hC hlam hbound htest hBm hBm).trans
  have hv := operatorField_energy_le hmB hC hbound hmm hm
  have hcoef : 0 ≤ 3 * lam := mul_nonneg (by norm_num) hlam
  have := mul_le_mul_of_nonneg_left (add_le_add hv hv) hcoef
  nlinarith
end
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]
theorem fluctuation_mean_zero 
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ∂μ.prod μ) = 0 := by
  have h₁ := (test_memLp_two hη hv₁).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₂ := (test_memLp_two hη hv₂).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₃ := (bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have ha := integral_add ((h₁.comp_fst μ).add (h₂.comp_snd μ)) h₃
  have hb := integral_add (h₁.comp_fst μ) (h₂.comp_snd μ)
  simp only [Pi.add_apply] at ha hb
  change (∫ z : Ω × Ω, test (M := M) η v₁ z.1 + test (M := M) η v₂ z.2 +
    bilinear (M := M) η B z ∂μ.prod μ) = 0
  have h_bilinear_mean_zero : (∫ z, bilinear (M := M) η B z ∂μ.prod μ) = 0 := by
    rw [integral_prod_symm _
      ((bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable (by norm_num))]
    apply integral_eq_zero_of_ae
    filter_upwards [memLp_sections hη] with y hy
    exact test_mean_zero hη hcenter (operatorField_memLp hmB hbound (hmη.comp (measurable_const.prodMk measurable_id)) hy)
  rw [ha, hb, integral_fun_fst, integral_fun_snd,
    test_mean_zero hη hcenter hv₁, test_mean_zero hη hcenter hv₂,
    h_bilinear_mean_zero]
  simp
theorem pilotMean_eq_fluctuation_ae (m ) (hmm : Measurable m) (hm : MemLp m 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫) :
    pilotMean (M := M) m η B =ᵐ[μ.prod μ]
      (fun z => fluctuation (M := M) η B (fun w => B w (m w))
        (fun w => B w (m w)) z + ∫ w, ⟪m w, B w (m w)⟫ ∂M) := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (memLp_sections hη),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (memLp_sections hη)] with z hx hy
  have := pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy
  linarith
theorem pilotMean_memLp_two (m ) (hmm : Measurable m) (hm : MemLp m 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    MemLp (pilotMean (M := M) m η B) 2 (μ.prod μ) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  exact ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).add
    (memLp_const (∫ w, ⟪m w, B w (m w)⟫ ∂M))).ae_eq
      (pilotMean_eq_fluctuation_ae m hmm hm hmη hη hmB hbound hsym).symm
theorem pilotMean_mean_eq (m ) (hmm : Measurable m) (hm : MemLp m 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, pilotMean (M := M) m η B z ∂μ.prod μ) = ∫ w, ⟪m w, B w (m w)⟫ ∂M := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  rw [integral_congr_ae (pilotMean_eq_fluctuation_ae m hmm hm hmη hη hmB hbound hsym), integral_add ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).integrable
    (by norm_num)) (integrable_const _),
    fluctuation_mean_zero hmη hη hcenter hmB hC hlam hbound htest hBm hBm]
  simp
end NearlyMinimax.PilotFields
namespace NearlyMinimax
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
variable {cB lam : ℝ}
theorem product_pairScoreOperator_integral 
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : E → ℝ} {Y' : F → ℝ} (hY : MemLp Y 2 μ) (hY' : MemLp Y' 2 ν)
    {f f' V : ℝ} (hm : (∫ x, Y x ∂μ) = f) (hm' : (∫ x, Y' x ∂ν) = f')
    (h2 : (∫ x, Y x ^ 2 ∂μ) = f ^ 2 + V)
    (h2' : (∫ x, Y' x ^ 2 ∂ν) = f' ^ 2 + V)
    (a b ) :
    (∫ z : E × F, ⟪a, pairScoreOperator V (Y z.1) (Y' z.2) b⟫ ∂μ.prod ν) =
      ⟪a, InnerProductSpace.rankOne ℝ (pairResponseVector f f') (pairResponseVector f f') b⟫ := by
  have hi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi' := hY'.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₀ := (hY'.integrable_sq.comp_snd μ).const_mul (a 0 * b 0)
  have h₁ := (hY.integrable_sq.comp_fst ν).const_mul (a 1 * b 1)
  have h₂ := (hi.mul_prod hi').const_mul (a 0 * b 1 + a 1 * b 0)
  have h₃ := (hi'.comp_snd μ).const_mul (a 0 * b 2 + a 2 * b 0)
  have h₄ := (hi.comp_fst ν).const_mul (a 1 * b 2 + a 2 * b 1)
  have h₅ : Integrable (fun _ => a 2 * b 2) (μ.prod ν) := integrable_const _
  have h₆ : Integrable (fun _ => V * (a 0 * b 0 + a 1 * b 1)) (μ.prod ν) :=
    integrable_const _
  have ha₀ := integral_add h₀ h₁
  have ha₁ := integral_add (h₀.add h₁) h₂
  have ha₂ := integral_add ((h₀.add h₁).add h₂) h₃
  have ha₃ := integral_add (((h₀.add h₁).add h₂).add h₃) h₄
  have ha₄ := integral_add ((((h₀.add h₁).add h₂).add h₃).add h₄) h₅
  have ha₅ := integral_sub (((((h₀.add h₁).add h₂).add h₃).add h₄).add h₅) h₆
  simp only [Pi.add_apply] at ha₀ ha₁ ha₂ ha₃ ha₄ ha₅
  simp_rw [pairScoreOperator_inner_polynomial]
  rw [ha₅, ha₄, ha₃, ha₂, ha₁, ha₀]
  have hs₀ : (∫ z : E × F, Y' z.2 ^ 2 ∂μ.prod ν) = f' ^ 2 + V := by
    calc
      _ = ∫ x, Y' x ^ 2 ∂ν := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_snd (μ := μ) (ν := ν) (fun x => Y' x ^ 2)
      _ = _ := h2'
  have hs₁ : (∫ z : E × F, Y z.1 ^ 2 ∂μ.prod ν) = f ^ 2 + V := by
    calc
      _ = ∫ x, Y x ^ 2 ∂μ := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_fst (μ := μ) (ν := ν) (fun x => Y x ^ 2)
      _ = _ := h2
  simp only [integral_const_mul, integral_fun_snd, integral_fun_fst, integral_prod_mul,
    hm, hm', hs₀, hs₁, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, integral_const,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner]
  rw [real_inner_comm b (pairResponseVector f f'), pairResponseVector_inner]
  ring
theorem conditional_pairScoreOperator_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun u : ℝ => u) 2 μ) (hν : MemLp (fun u : ℝ => u) 2 ν)
    (hmμ : (∫ u : ℝ, u ∂μ) = 0) (hmν : (∫ u : ℝ, u ∂ν) = 0)
     (h2μ : (∫ u : ℝ, u ^ 2 ∂μ) = V) (h2ν : (∫ u : ℝ, u ^ 2 ∂ν) = V)
    (f f' a b) :
    (∫ z : ℝ × ℝ, ⟪a, pairScoreOperator V (f + z.1) (f' + z.2) b⟫ ∂μ.prod ν) =
      ⟪a, InnerProductSpace.rankOne ℝ (pairResponseVector f f') (pairResponseVector f f') b⟫ := by
  have hY : MemLp (fun u => f + u) 2 μ := (memLp_const f).add hμ
  have hY' : MemLp (fun u => f' + u) 2 ν := (memLp_const f').add hν
  apply product_pairScoreOperator_integral μ ν hY hY' _ _
    (response_second_moment_of_centered_error hμ hmμ h2μ f)
    (response_second_moment_of_centered_error hν hmν h2ν f') a b
  · rw [integral_add (integrable_const _) (hμ.integrable (by norm_num)), hmμ]
    simp
  · rw [integral_add (integrable_const _) (hν.integrable (by norm_num)), hmν]
    simp
theorem observationPair_integral_conditioning  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d × Observation d → ℝ)
    (hg : Integrable g ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, g z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x : Covariate d × Covariate d,
        ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1),
          (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2)
        ∂(designLaw θ).prod (designLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have ho := measurePreserving_finTwoArrow (observationLaw θ)
  have he : ∀ x : Fin 2 → Covariate d,
      (∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
        ∂conditionalErrorLaw θ x) =
      ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1),
        (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1)) := by
    intro x
    have h := (measurePreserving_piFinTwo (fun i => θ.errors (x i))).integral_comp'
      (fun u => g ((x 0, θ.regression (x 0) + u.1),
        (x 1, θ.regression (x 1) + u.2)))
    exact h
  calc
    _ = ∫ z : Fin 2 → Observation d, g (z 0, z 1) ∂sampleLaw θ 2 :=
      (ho.integral_comp' g).symm
    _ = ∫ x : Fin 2 → Covariate d,
        ∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
          ∂conditionalErrorLaw θ x ∂designVectorLaw θ 2 := sampleLaw_integral_conditioning C θ hθ _ (ho.integrable_comp_of_integrable hg)
    _ = ∫ x : Fin 2 → Covariate d,
        ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1),
          (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1))
        ∂designVectorLaw θ 2 := by simp_rw [he]
    _ = _ := (measurePreserving_finTwoArrow (designLaw θ)).integral_comp' (fun x =>
      ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1),
        (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2))
def pairScoreFieldKernel  (θ : RegressionParameter d)
    (cA cB : Covariate d × Covariate d → PairVector)
    (q : Covariate d × Covariate d → ℝ) (z : Observation d × Observation d) : ℝ :=
  q (z.1.1, z.2.1) * ⟪cA (z.1.1, z.2.1),
    pairScoreOperator θ.variance z.1.2 z.2.2 (cB (z.1.1, z.2.1))⟫
def pairNoiseFieldKernel 
    (cA cB : Covariate d × Covariate d → PairVector)
    (q : Covariate d × Covariate d → ℝ) (z : Observation d × Observation d) : ℝ :=
  q (z.1.1, z.2.1) * ⟪cA (z.1.1, z.2.1), pairNoiseOperator (cB (z.1.1, z.2.1))⟫
variable {Ω : Type*} [MeasurableSpace Ω]
def pairPilotCoefficient  (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω)
    (w : Covariate d × Covariate d) : PairVector := bar w + η x w
def pairPilotScoreKernel  (θ : RegressionParameter d) (k ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) :
    Observation d × Observation d → ℝ :=
  pairScoreFieldKernel θ (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))
def pairPilotNoiseKernel  (k ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) :
    Observation d × Observation d → ℝ :=
  pairNoiseFieldKernel (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))
def pairPilotScoreMean  (θ : RegressionParameter d) (k ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) (k ^ d)
    (pairPilotScoreKernel θ k hk bar η) x
def pairPilotNoiseMean  (θ : RegressionParameter d) (k ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) (k ^ d)
    (pairPilotNoiseKernel k hk bar η) x
theorem pairPilotScoreMean_eq_half_pilotMean  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk bar)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω)
    (hi : Integrable (pairPilotScoreKernel θ k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    pairPilotScoreMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (boundedPairRegressionOperator C θ) x := by
  let := observationLaw_isProbability C θ hθ
  rw [pairPilotScoreMean, PairUStatistic.fieldPairMean]
  have h_pairScoreFieldKernel_mean (cA) (cB) (q) (hi : Integrable (pairScoreFieldKernel θ cA cB q) ((observationLaw θ).prod (observationLaw θ))) : (∫ z, pairScoreFieldKernel θ cA cB q z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x : Covariate d × Covariate d, q x * ⟪cA x,
        InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression x.1) (θ.regression x.2))
          (pairResponseVector (θ.regression x.1) (θ.regression x.2)) (cB x)⟫
        ∂(designLaw θ).prod (designLaw θ) := by
    let := designLaw_isProbability C θ hθ
    rw [observationPair_integral_conditioning C θ hθ _ hi]
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
        hθ.2.2.2.2.2.2.2,
      (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
        hθ.2.2.2.2.2.2.2] with x hx hx'
    change (∫ u : ℝ × ℝ, q x * ⟪cA x,
      pairScoreOperator θ.variance (θ.regression x.1 + u.1) (θ.regression x.2 + u.2) (cB x)⟫
        ∂(θ.errors x.1).prod (θ.errors x.2)) = _
    rw [integral_const_mul, conditional_pairScoreOperator_integral (θ.errors x.1) (θ.errors x.2)
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hx.2.1) ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hx'.2.1) hx.2.2.2.1 hx'.2.2.2.1 hx.2.2.2.2.1 hx'.2.2.2.2.1]
  change (k ^ d / 2) * (∫ z, pairPilotScoreKernel θ k hk bar η x z
    ∂(observationLaw θ).prod (observationLaw θ)) = _
  unfold pairPilotScoreKernel
  rw [((h_pairScoreFieldKernel_mean (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2) (sameLabelKernel (regularGridCell k hk)) hi))]
  have hM := regularPairDesignMeasure_integral C θ hθ k hk (fun w =>
    ⟪pairPilotCoefficient bar η x.1 w,
      InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairPilotCoefficient bar η x.2 w)⟫)
  rw [smul_eq_mul] at hM
  calc
    _ = (1 / 2) * (k ^ d * ∫ w, sameLabelKernel (regularGridCell k hk) w *
      ⟪pairPilotCoefficient bar η x.1 w,
        InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairResponseVector (θ.regression w.1) (θ.regression w.2))
            (pairPilotCoefficient bar η x.2 w)⟫ ∂(designLaw θ).prod (designLaw θ)) := by ring
    _ = (1 / 2) * (∫ w, ⟪pairPilotCoefficient bar η x.1 w,
      InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairPilotCoefficient bar η x.2 w)⟫ ∂regularPairDesignMeasure θ k hk) := by
      rw [hM]; rfl
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk] with w hw
      simp only [PilotFields.pilotMean, pairPilotCoefficient, hw]
theorem pairPilotNoiseMean_eq_half_pilotMean {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω)
    (hi : Integrable (pairPilotNoiseKernel k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    pairPilotNoiseMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (fun _ => pairNoiseOperator) x := by
  let := observationLaw_isProbability C θ hθ
  rw [pairPilotNoiseMean, PairUStatistic.fieldPairMean]
  have h_pairNoiseFieldKernel_mean (cA) (cB) (q) (hi : Integrable (pairNoiseFieldKernel cA cB q) ((observationLaw θ).prod (observationLaw θ))) : (∫ z, pairNoiseFieldKernel cA cB q z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x : Covariate d × Covariate d, q x * ⟪cA x, pairNoiseOperator (cB x)⟫
        ∂(designLaw θ).prod (designLaw θ) := by
    rw [observationPair_integral_conditioning C θ hθ _ hi]
    apply integral_congr_ae
    filter_upwards [] with x
    change (∫ _u : ℝ × ℝ, q x * ⟪cA x, pairNoiseOperator (cB x)⟫
      ∂(θ.errors x.1).prod (θ.errors x.2)) = _
    simp
  change (↑k ^ d / 2) * (∫ z, pairPilotNoiseKernel k hk bar η x z
    ∂(observationLaw θ).prod (observationLaw θ)) = _
  unfold pairPilotNoiseKernel
  rw [((h_pairNoiseFieldKernel_mean (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2) (sameLabelKernel (regularGridCell k hk)) hi))]
  have hM := regularPairDesignMeasure_integral C θ hθ k hk (fun w =>
    ⟪pairPilotCoefficient bar η x.1 w, pairNoiseOperator (pairPilotCoefficient bar η x.2 w)⟫)
  simp only [smul_eq_mul, pairPilotCoefficient] at hM
  simp only [PilotFields.pilotMean, pairPilotCoefficient]
  rw [hM]
  ring
section HalfMean
variable {W H : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]
theorem half_pilotMean_mean_eq (bar ) (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, PilotFields.test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ x, (1 / 2) * PilotFields.pilotMean (M := M) bar η B x ∂μ.prod μ) =
      (1 / 2) * ∫ w, ⟪bar w, B w (bar w)⟫ ∂M := by
  rw [integral_const_mul,
    PilotFields.pilotMean_mean_eq bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest]
theorem half_pilotMean_variance_transfer (bar ) (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
     (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
     (hmB : Measurable (fun z : W × H => B z.1 z.2))
     (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, PilotFields.test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    (G )
    (he : G =ᵐ[μ.prod μ] fun x => (1 / 2) * PilotFields.pilotMean (M := M) bar η B x) :
    MemLp G 2 (μ.prod μ) ∧
      (∫ x, (G x - ∫ z, G z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
        (3 / 4) * lam * cB ^ 2 * (2 * (∫ w, ‖bar w‖ ^ 2 ∂M) +
          ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have hHalf := (PilotFields.pilotMean_memLp_two bar hbarMeas hbar hmη hη hmB
    hcB hlam hbound hsym htest).const_mul (1 / 2 )
  refine ⟨hHalf.ae_eq he.symm, ?_⟩
  rw [integral_congr_ae (by filter_upwards [he] with x hx; rw [hx, integral_congr_ae he]), half_pilotMean_mean_eq bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest]
  have he : (fun x => ((1 / 2) * PilotFields.pilotMean (M := M) bar η B x -
      (1 / 2) * ∫ w, ⟪bar w, B w (bar w)⟫ ∂M) ^ 2) =
      (fun x => (1 / 4) * (PilotFields.pilotMean (M := M) bar η B x -
        ∫ w, ⟪bar w, B w (bar w)⟫ ∂M) ^ 2) := by funext x; ring
  rw [he, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (PilotFields.pilotMean_centered_sq_le bar hbarMeas hbar hmη hη hmB hcB hlam hbound hsym htest)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  convert h using 1 <;> ring
end HalfMean
theorem pairNoiseOperator_symmetric (a b ) :
    ⟪a, pairNoiseOperator b⟫ = ⟪pairNoiseOperator a, b⟫ := by
  rw [← real_inner_comm (pairNoiseOperator a) b, pairNoiseOperator_inner, pairNoiseOperator_inner]
  ring
theorem pairNoiseOperator_measurable_apply  [MeasurableSpace W] :
    Measurable (fun z : W × PairVector => pairNoiseOperator z.2) := by
  have h := pairNoiseOperator.continuous.measurable.comp
    (show Measurable (fun z : W × PairVector => z.2) from measurable_snd)
  exact h
section ActualMean
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector)
include C hθ
theorem pairPilotNoiseMean_mean_lower
    (hbarMeas : Measurable bar) (R )
    (hbarBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R)
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hmη : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2))
    (hη : MemLp (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2) 2
      (μ.prod (regularPairDesignMeasure θ k hk)))
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0)
    (lam ) (hlam : 0 ≤ lam)
    (htest : ∀ v : (Covariate d × Covariate d) → PairVector,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
      (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
        lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hi : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    (1 / 2 : ℝ) ≤ ∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound
  have hOp := PilotFields.operatorField_memLp pairNoiseOperator_measurable_apply
    (fun _ => pairNoiseOperator_norm_le) hbarMeas hbar
  have : (regularPairDesignMeasure θ k hk).real univ ≤
      ∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂regularPairDesignMeasure θ k hk := by
    have h := integral_mono_ae (integrable_const 1) (PilotFields.inner_integrable hbar hOp) (by
      filter_upwards [hfirst] with w hw
      rw [pairNoiseOperator_inner, hw]
      nlinarith [sq_nonneg (bar w 1)])
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  have h_pairPilotNoiseMean_mean_eq : (∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * ∫ w, (bar w 0) ^ 2 + (bar w 1) ^ 2 ∂regularPairDesignMeasure θ k hk := by
    let := regularPairDesignMeasure_isFinite C θ hθ k hk
    rw [integral_congr_ae (by filter_upwards [hi] with x hx; exact pairPilotNoiseMean_eq_half_pilotMean C θ hθ k hk bar η x hx), half_pilotMean_mean_eq bar hbarMeas (MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound) hmη hη hcenter
      pairNoiseOperator_measurable_apply (by norm_num : (0 : ℝ) ≤ 2) hlam
      (fun _ => pairNoiseOperator_norm_le) (fun _ => pairNoiseOperator_symmetric) htest]
    simp only [pairNoiseOperator_inner, pow_two]
  rw [h_pairPilotNoiseMean_mean_eq]
  have hEq : (∫ w, (bar w 0) ^ 2 + (bar w 1) ^ 2 ∂regularPairDesignMeasure θ k hk) =
      ∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂regularPairDesignMeasure θ k hk := by
    simp only [pairNoiseOperator_inner, pow_two]
  rw [hEq]
  linarith [(regularPairDesignMeasure_mass_bounds C θ hθ k hk).1]
end ActualMean
structure PairPilotMeanConditions {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (μ : Measure Ω) (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (R lam : ℝ) : Prop where
  barMeasurable : Measurable bar
  barBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R
  noiseMeasurable : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2)
  noiseMemLp : MemLp (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2) 2
    (μ.prod (regularPairDesignMeasure θ k hk))
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (Covariate d × Covariate d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk
  scoreConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotScoreKernel θ k hk bar η x)
    ((observationLaw θ).prod (observationLaw θ))
  noiseConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
    ((observationLaw θ).prod (observationLaw θ))
section ConcreteBounds
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (R lam : ℝ)
variable (hp : PairPilotMeanConditions θ k hk μ bar η R lam)
include C hθ hp
theorem pairPilotScoreMean_mean_eq :
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * ∫ w, ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫
        ∂regularPairDesignMeasure θ k hk := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  rw [integral_congr_ae (by filter_upwards [hp.scoreConditionalIntegrable] with x hx; exact pairPilotScoreMean_eq_half_pilotMean C θ hθ k hk bar η x hx)]
  exact half_pilotMean_mean_eq bar hp.barMeasurable (MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound) hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered
    (boundedPairRegressionOperator_measurable_apply C θ hθ) (by positivity) hp.lamNonnegative
    (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ) hp.linearTest
theorem pairPilotScoreMean_bias_le (b )
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) ≤ (C.densityUpper / 2) * b ^ 2 := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have hOp := PilotFields.operatorField_memLp (boundedPairRegressionOperator_measurable_apply C θ hθ)
    (boundedPairRegressionOperator_norm_le C θ) hp.barMeasurable hbar
  have hPoint : (fun w => ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫) ≤ᵐ[regularPairDesignMeasure θ k hk]
      (fun _ => b ^ 2) := by
    filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk, hresidual] with w hw hr
    rw [hw, InnerProductSpace.inner_right_rankOne_apply,
      real_inner_comm (bar w) (pairResponseVector (θ.regression w.1) (θ.regression w.2))]
    have hSq := pow_le_pow_left₀ (abs_nonneg _) hr 2
    rw [sq_abs] at hSq
    simpa only [pow_two] using hSq
  have hUpper := integral_mono_ae (PilotFields.inner_integrable hbar hOp) (integrable_const (b ^ 2)) hPoint
  simp only [integral_const, smul_eq_mul] at hUpper
  rw [pairPilotScoreMean_mean_eq C θ hθ k hk μ bar η R lam hp]
  calc
    _ ≤ (1 / 2) * ((regularPairDesignMeasure θ k hk).real univ * b ^ 2) :=
      mul_le_mul_of_nonneg_left hUpper (by norm_num)
    _ ≤ (1 / 2) * (C.densityUpper * b ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2 (sq_nonneg b))
      (by norm_num)
    _ = _ := by ring
theorem pairPilotScoreMean_mean_nonneg :
    0 ≤ ∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ := by
  rw [pairPilotScoreMean_mean_eq C θ hθ k hk μ bar η R lam hp]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro w
  change 0 ≤ ⟪bar w, InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2)) (bar w)⟫
  rw [InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm (bar w)
      (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))]
  exact mul_self_nonneg _
end ConcreteBounds
end NearlyMinimax
end
section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false
section
section
variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem operator_inner_sq_le (A : H →L[ℝ] H) (u v ) :
    ⟪u, A v⟫ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := (abs_real_inner_le_norm u (A v)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u))
  calc
    _ ≤ (‖u‖ * (‖A‖ * ‖v‖)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by ring
theorem product_operator_kernel_sq_integrable (A : H →L[ℝ] H)
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => ⟪f z.1, A (g z.2)⟫ ^ 2) (μ.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun z => ⟪f z.1, A (g z.2)⟫ ^ 2) (μ.prod μ) :=
    (hf.aestronglyMeasurable.comp_fst.inner
      (A.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable.comp_snd)).pow 2
  apply ((hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul (‖A‖ ^ 2)).mono' hm
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_assoc] using operator_inner_sq_le A (f z.1) (g z.2))
theorem product_operator_kernel_energy_le_uniform (A : H →L[ℝ] H)
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {L : ℝ} (hL : 0 ≤ L)
    (hEf : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ L) (hEg : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ L) :
    (∫ z : Ω × Ω, ⟪f z.1, A (g z.2)⟫ ^ 2 ∂μ.prod μ) ≤ ‖A‖ ^ 2 * L ^ 2 := by
  have h_product_operator_kernel_energy_le : (∫ z : Ω × Ω, ⟪f z.1, A (g z.2)⟫ ^ 2 ∂μ.prod μ) ≤
      ‖A‖ ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖g x‖ ^ 2 ∂μ := by
    calc
      _ ≤ ∫ z : Ω × Ω, ‖A‖ ^ 2 * (‖f z.1‖ ^ 2 * ‖g z.2‖ ^ 2) ∂μ.prod μ := by
        apply integral_mono (product_operator_kernel_sq_integrable A hf hg)
          ((hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul _)
        intro z
        simpa only [mul_assoc] using operator_inner_sq_le A (f z.1) (g z.2)
      _ = _ := by
        rw [integral_const_mul, integral_prod_mul (fun x => ‖f x‖ ^ 2) (fun x => ‖g x‖ ^ 2)]
        ring
  apply h_product_operator_kernel_energy_le.trans
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hEf (sq_nonneg ‖A‖))
    (integral_nonneg (μ := μ) (fun x : Ω => sq_nonneg ‖g x‖))
  have := mul_le_mul_of_nonneg_left hEg (mul_nonneg (sq_nonneg ‖A‖) hL)
  nlinarith
end
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]
def weightedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫ ^ 2
theorem weightedPilotKernel_section_integrable 
    {A : W → H →L[ℝ] H} {q : W → ℝ} {w : W}
    (hc : MemLp (fun x => c x w) 2 μ) :
    Integrable (fun z : Ω × Ω => weightedPilotKernel c A q (z, w)) (μ.prod μ) :=
  (product_operator_kernel_sq_integrable (A w) hc hc).const_mul (q w)
theorem weightedPilotKernel_section_energy_le 
    {A : W → H →L[ℝ] H} {q : W → ℝ} {w : W}
    (hc : MemLp (fun x => c x w) 2 μ) {L : ℝ} (hL : 0 ≤ L)
    (hE : (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) (hq : 0 ≤ q w) :
    (∫ z : Ω × Ω, weightedPilotKernel c A q (z, w) ∂μ.prod μ) ≤
      L ^ 2 * (q w * ‖A w‖ ^ 2) := by
  change (∫ z : Ω × Ω, q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2 ∂μ.prod μ) ≤ _
  rw [integral_const_mul]
  have := mul_le_mul_of_nonneg_left
    (product_operator_kernel_energy_le_uniform (A w) hc hc hL hE hE) hq
  nlinarith
theorem weightedPilotKernel_integrable 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ᵐ w ∂ν, 0 ≤ q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    Integrable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) := by
  have hi : Measurable (fun z : (Ω × Ω) × W =>
      ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫) :=
    (hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner
      (hmA.comp (measurable_snd.prodMk
        (hmc.comp (measurable_fst.snd.prodMk measurable_snd))))
  have hm : AEStronglyMeasurable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) :=
    ((hmq.comp measurable_snd).mul (hi.pow_const 2)).aestronglyMeasurable
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hc.mono (fun _ hw => weightedPilotKernel_section_integrable hw)
  · apply (hA.const_mul (L ^ 2)).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hc, hE, hq] with w hcw hEw hqw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    change (∫ z : Ω × Ω, ‖weightedPilotKernel c A q (z, w)‖ ∂μ.prod μ) ≤ _
    have hn : (fun z : Ω × Ω => ‖weightedPilotKernel c A q (z, w)‖) =
        (fun z : Ω × Ω => weightedPilotKernel c A q (z, w)) := by
      funext z
      change ‖q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2‖ =
        q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hqw (sq_nonneg _))]
    rw [hn]
    exact weightedPilotKernel_section_energy_le hcw hL hEw hqw
end
section
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]
def maskedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫
theorem maskedPilotKernel_measurable 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
     (hmq : Measurable q) : Measurable (maskedPilotKernel c A q) := by
  exact (hmq.comp measurable_snd).mul
    ((hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner
      (hmA.comp (measurable_snd.prodMk
        (hmc.comp (measurable_fst.snd.prodMk measurable_snd)))))
theorem maskedPilotKernel_sq_eq  {A : W → H →L[ℝ] H}
    {q : W → ℝ} (hq : ∀ w, q w ^ 2 = q w) (z : (Ω × Ω) × W) :
    maskedPilotKernel c A q z ^ 2 = weightedPilotKernel c A q z := by
  simp only [maskedPilotKernel, weightedPilotKernel, mul_pow, hq]
theorem maskedPilotKernel_memLp 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) := by
  apply (memLp_two_iff_integrable_sq
    (maskedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable).2
  simp_rw [maskedPilotKernel_sq_eq hq]
  exact weightedPilotKernel_integrable hmc hmA hmq
    (Filter.Eventually.of_forall (fun w => (hq w).symm ▸ sq_nonneg (q w))) hA hc hL hE
theorem maskedPilotKernel_energy_le 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  simp_rw [maskedPilotKernel_sq_eq hq]
  have hq : ∀ᵐ w ∂ν, 0 ≤ q w := Filter.Eventually.of_forall (fun w => (hq w).symm ▸ sq_nonneg (q w))
  have hi := weightedPilotKernel_integrable hmc hmA hmq hq hA hc hL hE
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right (hA.const_mul _)
  filter_upwards [hc, hE, hq] with w hcw hEw hqw
  exact weightedPilotKernel_section_energy_le hcw hL hEw hqw
end
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]
def restrictPilotField (c : Ω → W → H) (q : W → ℝ) (x : Ω) (w : W) : H :=
  if q w = 0 then 0 else c x w
theorem restrictPilotField_measurable {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) :
    Measurable (fun z : Ω × W => restrictPilotField c q z.1 z.2) :=
  Measurable.ite ((hmq.comp measurable_snd) (measurableSet_singleton 0))
    measurable_const hmc
theorem restrictPilotField_memLp {c : Ω → W → H} {q : W → ℝ}
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ) :
    ∀ᵐ w ∂ν, MemLp (fun x => restrictPilotField c q x w) 2 μ := by
  filter_upwards [hc] with w hw
  by_cases hq : q w = 0
  · simp [restrictPilotField, hq]
  · simpa [restrictPilotField, hq] using hw hq
theorem restrictPilotField_energy_le {c : Ω → W → H} {q : W → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    ∀ᵐ w ∂ν, (∫ x, ‖restrictPilotField c q x w‖ ^ 2 ∂μ) ≤ L := by
  filter_upwards [hE] with w hw
  by_cases hq : q w = 0
  · simpa [restrictPilotField, hq] using hL
  · simpa [restrictPilotField, hq] using hw hq
theorem maskedPilotKernel_restrict_eq (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) : maskedPilotKernel (restrictPilotField c q) A q = maskedPilotKernel c A q := by
  funext z
  by_cases hq : q z.2 = 0 <;> simp [maskedPilotKernel, restrictPilotField, hq]
theorem maskedPilotKernel_memLp_of_supported_sections 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact maskedPilotKernel_memLp (restrictPilotField_measurable hmc hmq) hmA hmq hq hA
    (restrictPilotField_memLp hc) hL (restrictPilotField_energy_le hL hE)
theorem maskedPilotKernel_energy_le_of_supported_sections 
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
     (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact maskedPilotKernel_energy_le (restrictPilotField_measurable hmc hmq) hmA hmq hq hA
    (restrictPilotField_memLp hc) hL (restrictPilotField_energy_le hL hE)
end NearlyMinimax.PilotFields
end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false
variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
theorem fieldPairAverage_memLp  (weight ) 
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (X ) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    MemLp (fieldPairAverage n weight G X) 2 (π.prod ν) := by
  unfold fieldPairAverage
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact ((hG.add (hG.comp_measurePreserving ((MeasurePreserving.id π).prod Measure.measurePreserving_swap))).const_mul (weight / 4)).comp_measurePreserving ((MeasurePreserving.id π).prod (pair_measurePreserving X hind hX ((Finset.mem_filter.mp hp).2)))
end NearlyMinimax.PairUStatistic
end
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace NearlyMinimax.PilotFields
open MeasureTheory
section
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]
theorem memLp_joint_of_uniform_section_energy {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M) := by
  apply (memLp_two_iff_integrable_sq_norm hmη.aestronglyMeasurable).2
  have hm : AEStronglyMeasurable (fun z : Ω × W => ‖η z.1 z.2‖ ^ 2) (μ.prod M) :=
    hmη.aestronglyMeasurable.norm.pow 2
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hη.mono (fun _ hw => hw.norm.integrable_sq)
  · apply (integrable_const R).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hE] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Function.comp_def, Prod.swap_prod_mk, norm_pow,
      Real.norm_eq_abs, sq_abs] using hw
theorem joint_energy_le_of_uniform_sections {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    (∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) ≤ R * M.real Set.univ := by
  have hi := (memLp_joint_of_uniform_section_energy hmη hη hR hE).norm.integrable_sq
  rw [integral_prod_symm _ hi]
  apply (integral_mono_ae hi.integral_prod_right (integrable_const R) hE).trans_eq
  simp [integral_const, mul_comm]
end
theorem pilot_coefficient_memLp_two  [MeasurableSpace Ω]
    [NormedAddCommGroup H]  [IsProbabilityMeasure μ]
    (u : H) {η : Ω → H} (hη : MemLp η 2 μ) :
    MemLp (fun x => u + η x) 2 μ := (memLp_const u).add hη
theorem pilot_coefficient_second_moment_le  [MeasurableSpace Ω]
    [NormedAddCommGroup H]  [IsProbabilityMeasure μ]
    (u : H) {η : Ω → H} (hη : MemLp η 2 μ) {C R : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hE : (∫ x, ‖η x‖ ^ 2 ∂μ) ≤ R) :
    (∫ x, ‖u + η x‖ ^ 2 ∂μ) ≤ 2 * C ^ 2 + 2 * R := by
  have hηi := hη.norm.integrable_sq
  calc
    _ ≤ ∫ x, 2 * ‖u‖ ^ 2 + 2 * ‖η x‖ ^ 2 ∂μ := by
      have h_norm_add_sq_le_twice (v : H) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
      exact integral_mono ((pilot_coefficient_memLp_two u hη).norm.integrable_sq) ((integrable_const _).add (hηi.const_mul 2))
        (fun x => (h_norm_add_sq_le_twice (η x)))
    _ = 2 * ‖u‖ ^ 2 + 2 * ∫ x, ‖η x‖ ^ 2 ∂μ := by
      rw [integral_add (integrable_const _) (hηi.const_mul 2), integral_const, integral_const_mul]
      simp
    _ ≤ _ := by
      have := pow_le_pow_left₀ (norm_nonneg u) hu 2
      linarith
end NearlyMinimax.PilotFields
namespace NearlyMinimax
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal
variable {d : ℕ}
section Partition
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (label : E → I) (hlabel : Measurable label)
  (r : E → ℝ) (hmr : Measurable r)
include hlabel hmr
def localizedResponseOperatorEnergy (V : ℝ) (z : E × E) : ℝ :=
  sameLabelKernel label z * ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2
theorem localizedResponseOperatorEnergy_integrable (V )
    (hr4 : Integrable (fun x => r x ^ 4) μ) :
    Integrable (localizedResponseOperatorEnergy label r V) (μ.prod μ) := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG : Integrable G (μ.prod μ) := labelLocalizedKernel_integrable μ label hlabel _ hr4
  have hi : Integrable (fun z =>
      6 * G z + 6 * G z.swap + (6 + 8 * V ^ 2) * sameLabelKernel label z) (μ.prod μ) :=
    ((hG.const_mul 6).add ((integrable_swap_iff.mpr hG).const_mul 6)).add (((sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)).const_mul _)
  have hm : Measurable (localizedResponseOperatorEnergy label r V) := by
    apply (sameLabelKernel_measurable label hlabel).mul
    have h_pairScoreOperator_continuous : Continuous (fun z : ℝ × ℝ => pairScoreOperator V z.1 z.2) := by
      exact ((InnerProductSpace.rankOne ℝ).continuous.comp pairResponseVector_continuous).clm_apply
        pairResponseVector_continuous |>.sub continuous_const
    exact (h_pairScoreOperator_continuous.measurable.comp
      ((hmr.comp measurable_fst).prodMk (hmr.comp measurable_snd))).norm.pow_const 2
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by unfold sameLabelKernel; split_ifs <;> norm_num) (sq_nonneg _))]
  by_cases he : label z.1 = label z.2
  · have hb := pairScoreOperator_norm_sq_le V (r z.1) (r z.2)
    simpa only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
      labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul, mul_one] using
      (show ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2 ≤
        6 * r z.2 ^ 4 + 6 * r z.1 ^ 4 + (6 + 8 * V ^ 2) by nlinarith [hb])
  · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
      he, Ne.symm he]
theorem localizedResponseOperatorEnergy_integral_le (V B4 )
    (hr4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ i : I, (∫ x, (label ⁻¹' {i}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      B4 * μ.real (label ⁻¹' {i})) :
    (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      (12 * B4 + 6 + 8 * V ^ 2) * ∑ i : I, μ.real (label ⁻¹' {i}) ^ 2 := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG  := labelLocalizedKernel_integrable μ label hlabel _ hr4
  have hGs : Integrable (fun z => G z.swap) (μ.prod μ) :=
    integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have := labelLocalizedKernel_integral_le μ label hlabel _ hr4 B4 hloc
  have hb : (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      ∫ z : E × E, 6 * G z + 6 * G z.swap +
        (6 + 8 * V ^ 2) * sameLabelKernel label z ∂μ.prod μ := by
    apply integral_mono (localizedResponseOperatorEnergy_integrable μ label hlabel r hmr V hr4)
      (((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _))
    intro z
    simp only [Pi.add_apply, Pi.mul_apply]
    by_cases he : label z.1 = label z.2
    · have hb := pairScoreOperator_norm_sq_le V (r z.1) (r z.2)
      simp only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
        labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul]
      nlinarith [hb]
    · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
        he, Ne.symm he]
  have ha := integral_add ((hG.const_mul 6).add (hGs.const_mul 6)) (hq.const_mul (6 + 8 * V ^ 2))
  have ha' := integral_add (hG.const_mul 6) (hGs.const_mul 6)
  simp only [Pi.add_apply, Pi.mul_apply] at ha ha'
  rw [ha, ha', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_swap G, sameLabelKernel_integral μ label hlabel] at hb
  nlinarith
end Partition
def responseOperatorEnergyBound  (C : ModelConstants d) : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2
theorem responseOperatorEnergyBound_pos  (C : ModelConstants d) :
    0 < responseOperatorEnergyBound C := by
  have := responseFourthBound_pos C
  unfold responseOperatorEnergyBound
  positivity
theorem regularResponseOperatorEnergy_integrable  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk) :
    Integrable (localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance) ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact localizedResponseOperatorEnergy_integrable (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
      (observationLaw_response_fourth_integrable C θ hθ)
def pairCovariates  (z : Observation d × Observation d) : Covariate d × Covariate d :=
  (z.1.1, z.2.1)
theorem pairCovariates_measurable (d ) : Measurable (pairCovariates (d := d)) :=
  measurable_fst.fst.prodMk measurable_snd.fst
theorem observationPair_covariates_measurePreserving  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving pairCovariates ((observationLaw θ).prod (observationLaw θ))
      ((designLaw θ).prod (designLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact (observationLaw_fst_measurePreserving C θ hθ).prod
    (observationLaw_fst_measurePreserving C θ hθ)
def rawModelPairScore   (θ : RegressionParameter d)
    (k ) (hk : 0 < k) (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), pairScoreOperator θ.variance z.1.2 z.2.2
      (c p.2 (pairCovariates z))⟫
theorem observationPairScoreOperator_measurable_apply  (V ) :
    Measurable (fun z : (Observation d × Observation d) × PairVector =>
      pairScoreOperator V z.1.1.2 z.1.2.2 z.2) := by
  have hv : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      pairResponseVector z.1.1.2 z.1.2.2) :=
    pairResponseVector_continuous.comp
      (continuous_fst.fst.snd.prodMk continuous_fst.snd.snd)
  have hi : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫) := hv.inner continuous_snd
  have hs : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫ • pairResponseVector z.1.1.2 z.1.2.2) := hi.smul hv
  simpa only [pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, starRingEnd_apply, star_trivial,
    Pi.sub_def, Pi.smul_def, Function.comp_def] using
    (hs.sub ((pairNoiseOperator.continuous.comp continuous_snd).const_smul V)).measurable
theorem pilotOnObservations_measurable  [MeasurableSpace Ω] 
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : Ω × (Observation d × Observation d) => c z.1 (pairCovariates z.2)) :=
  hmc.comp (measurable_fst.prodMk ((pairCovariates_measurable d).comp measurable_snd))
theorem rawModelPairScore_measurable  [MeasurableSpace Ω] 
    (θ : RegressionParameter d) (k hk)
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairScore θ k hk c z.1 z.2) := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
theorem rawModelPairScore_memLp  [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π]  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk)
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
     (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairScore θ k hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  · intro z
    unfold sameLabelKernel
    split_ifs <;> norm_num
  · exact regularResponseOperatorEnergy_integrable C θ hθ k hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE
theorem rawModelPairScore_energy_le  [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π]  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk)
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
     (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    (∫ z : (Ω × Ω) × (Observation d × Observation d), rawModelPairScore θ k hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (responseOperatorEnergyBound C * (C.densityUpper / ↑k ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (regularResponseOperatorEnergy_integrable C θ hθ k hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  have h_regularResponseOperatorEnergy_le : (∫ z, localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance z ∂(observationLaw θ).prod (observationLaw θ)) ≤
      responseOperatorEnergyBound C * (C.densityUpper / k ^ d) := by
    let := observationLaw_isProbability C θ hθ
    have hb := localizedResponseOperatorEnergy_integral_le (observationLaw θ) _
      (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
      (responseFourthBound C) (observationLaw_response_fourth_integrable C θ hθ) (by
        intro i
        rw [regularObservationLabel_mass C θ hθ k hk i, regularObservationLabel_fiber k hk i]
        exact observationLaw_localized_fourth_integral_le C θ hθ _
          ((measurableSet_singleton i).preimage (regular_grid_cell_measurable k hk)))
    simp_rw [regularObservationLabel_mass C θ hθ k hk] at hb
    have : θ.variance ^ 2 ≤ C.varianceUpper ^ 2 := pow_le_pow_left₀ (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) (hθ.2.2.2.2.2.2.1) 2
    change _ ≤ (12 * responseFourthBound C + 6 + 8 * θ.variance ^ 2) *
      regularGridCollisionMass θ k hk at hb
    apply hb.trans
    calc
      _ ≤ responseOperatorEnergyBound C * regularGridCollisionMass θ k hk := by
        apply mul_le_mul_of_nonneg_right _ (by unfold regularGridCollisionMass; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        unfold responseOperatorEnergyBound
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk)
        (responseOperatorEnergyBound_pos C).le
  exact he.trans (mul_le_mul_of_nonneg_left h_regularResponseOperatorEnergy_le
    (sq_nonneg L))
theorem observationPairNoiseOperator_energy_integrable  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (fun z : Observation d × Observation d =>
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2)
      ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact ((sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk)).integrable (by norm_num)).mul_const _
def rawModelPairNoise   (k ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), pairNoiseOperator (c p.2 (pairCovariates z))⟫
theorem rawModelPairNoise_measurable  [MeasurableSpace Ω] 
    (k hk) 
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairNoise k hk c z.1 z.2) := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
theorem rawModelPairNoise_memLp  [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π]  (C θ) (hθ : Admissible C θ) (k hk)
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
     (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    MemLp (fun z => rawModelPairNoise k hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  · intro z
    unfold sameLabelKernel
    split_ifs <;> norm_num
  · exact observationPairNoiseOperator_energy_integrable C θ hθ k hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE
theorem rawModelPairNoise_energy_le  [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π]  (C : ModelConstants d)
    (θ ) (hθ : Admissible C θ) (k hk)
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
     (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    (∫ z : (Ω × Ω) × (Observation d × Observation d), rawModelPairNoise k hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (4 * (C.densityUpper / k ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (observationPairNoiseOperator_energy_integrable C θ hθ k hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  have h_observationPairNoiseOperator_energy_le : (∫ z : Observation d × Observation d,
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤ 4 * (C.densityUpper / k ^ d) := by
    let := observationLaw_isProbability C θ hθ
    rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _
      (regularObservationLabel_measurable k hk)]
    simp_rw [regularObservationLabel_mass C θ hθ k hk]
    have hq : 0 ≤ regularGridCollisionMass θ k hk := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2
    calc
      _ ≤ regularGridCollisionMass θ k hk * 4 := mul_le_mul_of_nonneg_left (by norm_num at h; exact h) hq
      _ ≤ _ := by have := regularGridCollisionMass_upper C θ hθ k hk; linarith
  exact he.trans (mul_le_mul_of_nonneg_left h_observationPairNoiseOperator_energy_le
    (sq_nonneg L))
theorem regularPairDesignMeasure_ae_of_supported 
    (θ k hk)
    {P : Covariate d × Covariate d → Prop}
    (hp : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → P w) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, P w := by
  change ∀ᵐ w ∂ENNReal.ofReal (↑k ^ d) •
    ((designLaw θ).prod (designLaw θ)).restrict
      {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}, P w
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))).2
  filter_upwards [hp] with w hw hs
  apply hw
  have hs' : regularGridCell k hk w.1 = regularGridCell k hk w.2 := hs
  simp [sameLabelKernel, hs']
structure PairPilotAssumptions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ) : Prop where
  constantNonnegative : 0 ≤ Cp
  budgetNonnegative : 0 ≤ W
  barMeasurable : Measurable bar
  noiseMeasurable : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2)
  barBound : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp
  noiseSection : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => η x w) 2 μ
  noiseEnergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ Cp * W
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (Covariate d × Covariate d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk
section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hp
theorem pairPilotCoefficient_measurable :
    Measurable (fun z : Ω × (Covariate d × Covariate d) => pairPilotCoefficient bar η z.1 z.2) :=
  (hp.barMeasurable.comp measurable_snd).add hp.noiseMeasurable
theorem pairPilotCoefficient_sections :
    ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => pairPilotCoefficient bar η x w) 2 μ := by
  filter_upwards [hp.noiseSection] with w hw hs
  exact PilotFields.pilot_coefficient_memLp_two (bar w) (hw hs)
theorem pairPilotCoefficient_energy :
    ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, ‖pairPilotCoefficient bar η x w‖ ^ 2 ∂μ) ≤ 2 * Cp ^ 2 + 2 * Cp * W := by
  filter_upwards [hp.noiseSection, hp.barBound, hp.noiseEnergy] with w hs hb he hq
  simpa only [pairPilotCoefficient, mul_assoc] using
    PilotFields.pilot_coefficient_second_moment_le (bar w) (hs hq)
      hp.constantNonnegative (hb hq) (he hq)
include C hθ
theorem pairPilotScoreKernel_memLp :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      pairPilotScoreKernel θ k hk bar η z.1 z.2) 2
      ((μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) := by
  exact rawModelPairScore_memLp μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative] : 0 ≤ 2 * Cp ^ 2 + 2 * Cp * W)
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)
theorem pairPilotNoiseKernel_memLp :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      pairPilotNoiseKernel k hk bar η z.1 z.2) 2
      ((μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) := by
  exact rawModelPairNoise_memLp μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative] : 0 ≤ 2 * Cp ^ 2 + 2 * Cp * W)
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)
theorem pairPilotAssumptions_meanConditions :
    PairPilotMeanConditions θ k hk μ bar η Cp lam := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  let := observationLaw_isProbability C θ hθ
  refine ⟨hp.barMeasurable, regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound,
    hp.noiseMeasurable, ?_, hp.noiseCentered, hp.lamNonnegative, hp.linearTest, ?_, ?_⟩
  · exact PilotFields.memLp_joint_of_uniform_section_energy hp.noiseMeasurable (regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection)
      (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) (regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy)
  · exact ((pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae
  · exact ((pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae
end
end NearlyMinimax
