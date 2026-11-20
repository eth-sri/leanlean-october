module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Product-pilot kernel energies. Independence is implemented by the actual
product measure; the second moment bound is derived from the two pilot L²
energies rather than supplied as a kernel-moment assumption. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section
variable (A : H →L[ℝ] H)

theorem operator_inner_sq_le (u v : H) :
    ⟪u, A v⟫ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := (abs_real_inner_le_norm u (A v)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u))
  calc
    _ ≤ (‖u‖ * (‖A‖ * ‖v‖)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by ring

theorem product_operator_kernel_moments
    {f : Ω → H} (hf : MemLp f 2 μ) :
    Integrable (fun z : Ω × Ω => ⟪f z.1, A (f z.2)⟫ ^ 2) (μ.prod μ) ∧
    (∫ z : Ω × Ω, ⟪f z.1, A (f z.2)⟫ ^ 2 ∂μ.prod μ) ≤
      ‖A‖ ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) ^ 2 := by
  have hm : AEStronglyMeasurable
      (fun z : Ω × Ω => ⟪f z.1, A (f z.2)⟫ ^ 2) (μ.prod μ) :=
    (hf.aestronglyMeasurable.comp_fst.inner
      (A.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable.comp_snd)).pow 2
  have hi := (hf.norm.integrable_sq.mul_prod hf.norm.integrable_sq).const_mul (‖A‖ ^ 2)
  have hb (z : Ω × Ω) : ⟪f z.1, A (f z.2)⟫ ^ 2 ≤ ‖A‖ ^ 2 * (‖f z.1‖ ^ 2 * ‖f z.2‖ ^ 2) := by
    simpa only [mul_assoc] using operator_inner_sq_le A (f z.1) (f z.2)
  have hK := hi.mono' hm (.of_forall fun z => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hb z)
  refine ⟨hK, (integral_mono hK hi hb).trans_eq ?_⟩
  rw [integral_const_mul, integral_prod_mul (fun x => ‖f x‖ ^ 2) (fun x => ‖f x‖ ^ 2)]
  ring

end
end NearlyMinimax.PilotFields
