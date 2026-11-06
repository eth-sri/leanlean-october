module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaQuadraticRemainder
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Local derivative budgets for the actual quadratic remainder

Only derivatives on the central interval are used. The actual globally
smooth weight is retained, so this can be applied where the original
cutoff is constant without paying its remote transition derivatives.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem abs_segmentTaylorAverage_le_closed
    {f : ℝ → ℝ} {l r a x M : ℝ}
    (ha : a ∈ Icc l r) (hx : x ∈ Icc l r) (k : ℕ)
    (hb : ∀ u ∈ Icc l r, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖(1-t)*t^k*iteratedDeriv k f (a+t*(x-a))‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hf : 0 ≤ (1-t)*t^k := mul_nonneg (by grind) (pow_nonneg ht.1 k)
    pm_1627
    have hseg : a+t*(x-a) ∈ Icc l r := by
      have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.1)
      have h₂ := mul_nonneg ht.1 (sub_nonneg.mpr hx.1)
      have h₃ := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2)
      have h₄ := mul_nonneg ht.1 (sub_nonneg.mpr hx.2)
      grind
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hf]
    exact (mul_le_of_le_one_left (norm_nonneg _) hf').trans (hb _ hseg)
  have h := norm_integral_le_of_norm_le_const hpoint
  aesop

section
variable {W : ℝ → ℝ} {H M z : ℝ}
include W H M z
theorem abs_quadraticTaylorCoefficient_le_local
    (hH : 0 ≤ H) (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 2 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |quadraticTaylorCoefficient W z| ≤ M := by
  apply abs_segmentTaylorAverage_le_closed (show (0 : ℝ) ∈ Icc (-H) H by constructor <;> linarith) hz 0
  intro x hx
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb x hx

theorem abs_deriv_quadraticTaylorCoefficient_le_local
    (hW : ContDiff ℝ ∞ W) (hH : 0 ≤ H)
    (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 3 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |deriv (quadraticTaylorCoefficient W) z| ≤ M := by
  rw [quadraticTaylorCoefficient_deriv hW]
  apply abs_segmentTaylorAverage_le_closed (show (0 : ℝ) ∈ Icc (-H) H by constructor <;> linarith) hz 1
  intro x hx
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb x hx
end

theorem norm_integral_sq_mul_betaQuadraticKernel_le_local
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z ∈ Icc (-H) H, |V z| ≤ M)
    (hd : ∀ z ∈ Icc (-H) H, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) := by
  pm_1635
  have hU : ∀ z : ℝ, HasDerivAt U (U' z) z := by
    pb_2543
    pm_124 U U' Pi.mul_def id_eq one_mul h
  pm_1633
  have hUb : ∀ z : ℝ, |z| ≤ H → ‖U z*betaQuadraticKernel T z‖ ≤ H*M := by
    intro z hz
    pm_502 norm_mul norm_betaQuadraticKernel mul_one Complex.norm_real Real.norm_eq_abs abs_mul
    exact mul_le_mul hz (hb z (abs_le.mp hz)) (abs_nonneg _) hH.le
  have hIb : ‖∫ z in (-H)..H, U' z*betaQuadraticKernel T z‖ ≤ 2*H*(M+H*L) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -H) (b := H) (f := fun z : ℝ => U' z*betaQuadraticKernel T z) (C := M+H*L) (fun z hz => by
        pm_1636
        exact (abs_add_le (V z) (z*deriv V z)).trans
          (add_le_add (hb z (abs_le.mp hz')) (by
            rw [abs_mul]
            exact mul_le_mul hz' (hd z (abs_le.mp hz')) (abs_nonneg _) hH.le)))
    pm_6210
  pm_1634

theorem norm_quadratic_window_remainder_le_local
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have hparts := norm_integral_sq_mul_betaQuadraticKernel_le_local
    (quadraticTaylorCoefficient_contDiff hW) hT hH
    (fun z hz => abs_quadraticTaylorCoefficient_le_local hH.le h₂ hz)
    (fun z hz => abs_deriv_quadraticTaylorCoefficient_le_local hW hH.le h₃ hz)
  pb_160

theorem quadraticRemainderConstant_le_inverse_window
    {H M₀ M₂ M₃ : ℝ} (hH : 0 < H) (hH₁ : H ≤ 1)
    (h₂ : 0 ≤ M₂) (h₃ : 0 ≤ M₃) :
    quadraticRemainderConstant H M₀ M₂ M₃ ≤
      (4*M₀/Real.pi+(4*M₂+2*M₃)/(2*Real.pi))/H := by
  have hH₂ : H^2 ≤ 1 := pow_le_one₀ hH.le hH₁
  have hH₃ : H^3 ≤ 1 := pow_le_one₀ hH.le hH₁
  have hb : 4*H^2*M₂+2*H^3*M₃ ≤ 4*M₂+2*M₃ := by
    nlinarith [mul_le_mul_of_nonneg_right hH₂ h₂,mul_le_mul_of_nonneg_right hH₃ h₃]
  apply (le_div_iff₀ hH).mpr
  have he : quadraticRemainderConstant H M₀ M₂ M₃*H =
      4*M₀/Real.pi+(4*H^2*M₂+2*H^3*M₃)/(2*Real.pi) := by
    unfold quadraticRemainderConstant
    field_simp
    ring
  rw [he]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hb (by positivity))

end TaoTrudgianYang2025
