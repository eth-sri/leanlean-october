module

public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Product-pilot kernel energies. Independence is implemented by the actual
product measure; the second moment bound is derived from the two pilot L²
energies rather than supplied as a kernel-moment assumption. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

variable {Ω H : Type*} [MeasurableSpace Ω]
𝛓
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

𝗇 𝔅 H →L[ℝ] H
𝗇 𝔇 ‖A‖ ^ 2
theorem operator_inner_sq_le (A : 𝔅) u v :
    ⟪u, A v⟫ ^ 2 ≤ 𝔇 * 𝘌₂ ^ 2 * 𝚡₁ ^ 2 := by
  have h := (abs_real_inner_le_norm u $ A v ).trans
    $ mul_le_mul_of_nonneg_left (A.le_opNorm v) $ norm_nonneg u
  calc
    _ ≤ (𝘌₂ * (‖A‖ * 𝚡₁)) ^ 2 := by
      simpa only [sq_abs] using 𝗂 h 2
    𝘿 := 𝖢₃

𝗇 𝔄 ⟪f z.1, A $ g z.2 ⟫ ^ 2
𝗇 𝔊 operator_inner_sq_le A (f z.1) $ g z.2
𝗇 𝔎 fun z => 𝔄
𝗇 𝔐 MemLp f 2 μ
𝗇 𝔑 MemLp g 2 μ
theorem product_operator_kernel_sq_integrable (A : 𝔅)
    (hf : 𝔐) (hg : 𝔑) :
    Integrable 𝔎 $ μ.prod μ := by
  have hm : AEStronglyMeasurable
      𝔎 $ μ.prod μ :=
    (hf.aestronglyMeasurable.comp_fst.inner
      $ A.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable.comp_snd ).pow 2
  have hi := (hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul 𝔇
  apply hi.mono' hm
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, 𝗤]
    simpa only [mul_assoc] using 𝔊

𝗃 𝔓 ‖f ἀ‖ ^ 2
𝗇 𝔈 ∫ x, 𝔓 x ∂μ
𝗇 𝔒 ‖g x‖
𝗇 𝔉 ∫ x, 𝔒 ^ 2 ∂μ
𝗇 𝔍 ∫ z : 𝚎, 𝔄 ∂μ.prod μ
theorem product_operator_kernel_energy_le (A : 𝔅)
    (hf : 𝔐) (hg : 𝔑) :
    𝔍 ≤
      𝔇 * 𝔈 * 𝔉 := by
  calc
    _ ≤ ∫ z : 𝚎, 𝔇 * (𝔓 z.1 * ‖g z.2‖ ^ 2) ∂μ.prod μ := by
      apply integral_mono (product_operator_kernel_sq_integrable A hf hg)
        $ (hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul _
      intro z
      simpa only [mul_assoc] using 𝔊
    𝘿 := by
      rw [integral_const_mul, integral_prod_mul (fun x => 𝔓 x) fun x => 𝔒 ^ 2 ]
      ring

𝗇 𝔏 sq_nonneg ‖A‖
theorem product_operator_kernel_energy_le_uniform (A : 𝔅)
    (hf : 𝔐) (hg : 𝔑)
    (hL : 𝘨)
    (hEf : 𝔈 ≤ L) (hEg : 𝔉 ≤ L) :
    𝔍 ≤ 𝔇 * 𝖱₂ := by
  apply (product_operator_kernel_energy_le A hf hg).trans
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hEf 𝔏)
    $ integral_nonneg (μ := μ) fun x => sq_nonneg 𝔒
  have h2 := mul_le_mul_of_nonneg_left hEg $ mul_nonneg 𝔏 hL
  nlinarith
