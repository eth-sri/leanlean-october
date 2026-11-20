module

public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DedekindZetaZeroFree.FourierContinuation.ResidualScalarNorm
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (f : X → ℂ) (hf : MemLp f 2 μ)

include hf in
theorem pairing_self_eq_lpNorm_sq :
    (∫x, star (f x)*f x ∂μ) = ((lpNorm f 2 μ)^2 : ℝ) := by
  have he : (∫x, star (f x)*f x ∂μ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    exact mul_comm _ _
  simp_all [lpNorm]

include hf in
theorem norm_pairing_self :
    ‖∫x, star (f x)*f x ∂μ‖ = (lpNorm f 2 μ)^2 := by
  rw [pairing_self_eq_lpNorm_sq f hf]
  simp

include hf in
theorem lpNorm_le_of_pairing_bound
    (B p : ℝ) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (h : ‖∫x, star (f x)*f x ∂μ‖ ≤ B*p^2) :
    lpNorm f 2 μ ≤ Real.sqrt B*p := by
  rw [norm_pairing_self f hf] at h
  have hr := mul_nonneg (Real.sqrt_nonneg B) hp
  have he : (Real.sqrt B*p)^2 = B*p^2 := by rw [mul_pow, (Real.sq_sqrt hB)]
  nlinarith

end DedekindZetaZeroFree.FourierContinuation.ResidualScalarNorm

end
