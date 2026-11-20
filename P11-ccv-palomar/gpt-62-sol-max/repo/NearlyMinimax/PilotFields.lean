module

public import NearlyMinimax.LocalizationL2
public import NearlyMinimax.ProductSectionBounds


@[expose] public section

/-! Pilot fields remain ordinary jointly measurable functions. The scalar
test and independent-pilot bounds below do not assume measurability of a
random map into an L² quotient space. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

section
variable {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M)
include hf hg

theorem toLp_inner :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ w, ⟪f w, g w⟫ ∂M := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  simp_all

theorem inner_integral_sq_le :
    (∫ w, ⟪f w, g w⟫ ∂M) ^ 2 ≤
      (∫ w, ‖f w‖ ^ 2 ∂M) * (∫ w, ‖g w‖ ^ 2 ∂M) := by
  simp_rw [← real_inner_self_eq_norm_sq, ← toLp_inner hf hg, ← toLp_inner hf hf,
    ← toLp_inner hg hg, real_inner_self_eq_norm_sq]
  calc
    _ ≤ (‖hf.toLp f‖ * ‖hg.toLp g‖) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)) 2
    _ = _ := by ring

theorem inner_integrable :
    Integrable (fun w => ⟪f w, g w⟫) M := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  simp_all

end

def test (η : Ω → W → H) (v : W → H) (x : Ω) : ℝ :=
  ∫ w, ⟪η x w, v w⟫ ∂M

section
variable {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
include hη

theorem memLp_sections :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M := by
  filter_upwards [hη.aestronglyMeasurable.prodMk_left,
    hη.norm.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

section
variable {v : W → H} (hv : MemLp v 2 M)
include hv

theorem test_aestronglyMeasurable :
    AEStronglyMeasurable (test (M := M) η v) μ := by
  have hm : AEStronglyMeasurable
      (fun z : Ω × W => ⟪η z.1 z.2, v z.2⟫) (μ.prod M) :=
    hη.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd
  exact hm.integral_prod_right'

theorem test_sq_integrable :
    Integrable (fun x => test (M := M) η v x ^ 2) μ := by
  have hi := hη.norm.integrable_sq.integral_prod_left.mul_const
    (∫ w, ‖v w‖ ^ 2 ∂M)
  apply hi.mono' ((test_aestronglyMeasurable hη hv).pow 2)
  filter_upwards [memLp_sections hη] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact inner_integral_sq_le hx hv

theorem test_memLp_two :
    MemLp (test (M := M) η v) 2 μ :=
  (memLp_two_iff_integrable_sq (test_aestronglyMeasurable hη hv)).2
    (test_sq_integrable hη hv)

end

end

/-- Pointwise mean centering implies centering against every deterministic
L² test, with the Fubini integrability obligation proved. -/
theorem test_mean_zero [CompleteSpace H] {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M)
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0) :
    (∫ x, test (M := M) η v x ∂μ) = 0 := by
  have hcomp : MemLp (fun z : Ω × W => v z.2) 2 (μ.prod M) :=
    hv.comp_measurePreserving measurePreserving_snd
  have hi := inner_integrable hη hcomp
  change (∫ x, ∫ w, ⟪η x w, v w⟫ ∂M ∂μ) = 0
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hcenter, hη.aestronglyMeasurable.prodMk_right,
    hη.norm.integrable_sq.prod_left_ae] with w hw hm hisq
  have hηw :=
    (memLp_two_iff_integrable_sq_norm hm).2 hisq
  calc
    (∫ x, ⟪η x w, v w⟫ ∂μ) = ∫ x, ⟪v w, η x w⟫ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => real_inner_comm _ _)
    _ = ⟪v w, ∫ x, η x w ∂μ⟫ := integral_inner (hηw.integrable (by norm_num)) _
    _ = 0 := by simp [hw]

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M

theorem bilinear_measurable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2)) :
    Measurable (bilinear (M := M) η B) := by
  have hm : Measurable (fun z : (Ω × Ω) × W =>
      ⟪η z.1.1 z.2, B z.2 (η z.1.2 z.2)⟫) := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

section
variable {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ}
include hmB

omit hmB in
private theorem operatorField_norm_le (hbound : ∀ w, ‖B w‖ ≤ C) (w : W) (x : H) :
    ‖B w x‖ ≤ C * ‖x‖ :=
  ((B w).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))

section
variable (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M)
include hbound hmf hf

theorem operatorField_memLp :
    MemLp (fun w => B w (f w)) 2 M :=
  hf.of_le_mul (c := C) (hmB.comp (measurable_id.prodMk hmf)).aestronglyMeasurable
    (.of_forall fun w => operatorField_norm_le hbound w (f w))

theorem operatorField_energy_le :
    (∫ w, ‖B w (f w)‖ ^ 2 ∂M) ≤ C ^ 2 * ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← integral_const_mul]
  refine integral_mono (operatorField_memLp hmB hbound hmf hf).norm.integrable_sq
    (hf.norm.integrable_sq.const_mul _) fun w => ?_
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (operatorField_norm_le hbound w (f w)) 2

end

end

/-- A uniform second-moment bound for the linear tests of a pilot field. -/
abbrev TestEnergyBound (η : Ω → W → H) (lam : ℝ) : Prop :=
  ∀ v : W → H, MemLp v 2 M →
    (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M

section
variable [CompleteSpace H]
variable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : TestEnergyBound (μ := μ) (M := M) η lam)
include hmη hη hmB hlam hbound htest

/-- Apply the tested bound to the random second pilot after conditioning on it. -/
theorem bilinear_moments :
    MemLp (bilinear (M := M) η B) 2 (μ.prod μ) ∧
    (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ) ≤
      lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M := by
  have hm := (bilinear_measurable (M := M) hmη hmB).aestronglyMeasurable (μ := μ.prod μ)
  have hs := hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C^2)
  obtain ⟨hi, hb⟩ := integrable_prod_and_integral_le (hm.pow 2) hs (by
    filter_upwards [memLp_sections hη] with y hy
    have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
    have hv := operatorField_memLp hmB hbound hmy hy
    refine ⟨test_sq_integrable hη hv, fun _ => sq_nonneg _, ?_⟩
    exact (htest _ hv).trans (by rw [mul_assoc]; gcongr; exact operatorField_energy_le hmB hbound hmy hy))
  rw [integral_const_mul, ← integral_prod _ hη.norm.integrable_sq] at hb
  exact ⟨(memLp_two_iff_integrable_sq hm).2 hi, hb⟩

omit hlam htest in
theorem bilinear_mean_zero
    (hL : MemLp (bilinear (M := M) η B) 2 (μ.prod μ))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0) :
    (∫ z, bilinear (M := M) η B z ∂μ.prod μ) = 0 := by
  rw [integral_prod_symm _ (hL.integrable (by norm_num))]
  apply integral_eq_zero_of_ae
  filter_upwards [memLp_sections hη] with y hy
  have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  exact test_mean_zero hη (operatorField_memLp hmB hbound hmy hy) hcenter

end
end OperatorField
end NearlyMinimax.PilotFields
