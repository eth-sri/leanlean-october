module
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Compact.MeasuredMarginR01
public import Glennie.Theorems.Frames

@[expose] public section
namespace Glennie.Compact.NativeDefectReadoutR01
open Glennie
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NormCompatibleNullTargetR01
open Glennie.Compact.MeasuredMarginR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
section
@[simp] theorem native_response_eq (x y z : Albert) :
    response jordanLinear x y z = phi x y z := by
  simp only [response, phiWith, phi, jordanLinear_apply_apply, quadraticWith, U,
    show (Inner.inner ℝ : Albert → Albert → ℝ) = Glennie.inner from rfl]

/-- All trace-one orthogonal frames have the same encoder radius. -/
theorem frame_encoder_radius (p : Fin 3 → Albert) (hp : Frame p) :
    ‖encoder p‖ ≤ Real.sqrt 2 :=
  Real.le_sqrt_of_sq_le ((native_norm_sq _).trans (frame_encoder_norm p hp)).le

/-- Convert the common radius-two scalar estimate to a six-readout defect bound. -/
theorem frame_scalar_defect_lower (noisy : Readouts) (ε μ : ℝ)
    (h : |noisyPhi noisy|-6*ε ≤ 38*μ*(Real.sqrt 2)^9) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have hs : (Real.sqrt (2:ℝ))^9 = 16*Real.sqrt 2 := by grind
  norm_num [noisyPhi, abs_div, hs] at h
  apply (div_le_iff₀ (by positivity : 0 < 1216*Real.sqrt (2:ℝ))).2
  nlinarith

/-- Shared measured-defect estimate for a norm-compatible null target. -/
theorem frame_defect_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hnull : ∀ a b c, response jE a b c = 0)
    (T : Glennie.Compact.Affine20.Triple) (hT : ∀ a, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert, ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  have h := response_discrepancy_radius jordanLinear jE f jordan_norm hE U_norm hUE
    μ hμ hdef (Real.sqrt 2) (Real.sqrt_nonneg 2)
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
    (frame_encoder_radius _ (hT 0)) (frame_encoder_radius _ (hT 1)) (frame_encoder_radius _ (hT 2))
  rw [native_response_eq, hnull, sub_zero] at h
  exact frame_scalar_defect_lower noisy ε μ
    ((scalar_margin_lower _ _ _ (six_readout_scalar_error T noisy ε (6 * ε) hreadout le_rfl)).trans h)

end
end Glennie.Compact.NativeDefectReadoutR01
