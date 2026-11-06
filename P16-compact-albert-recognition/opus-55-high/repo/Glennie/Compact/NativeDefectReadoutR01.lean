module
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Compact.MeasuredMarginR01
public import Glennie.Theorems.Frames

@[expose] public section
namespace Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.MeasuredMarginR01
open Glennie.Compact.ReadoutRobustnessR01

@[simp] theorem native_Q_eq (a b : Albert) : Q jordanLinear a b = U a b := rfl

@[simp] theorem native_response_eq (x y z : Albert) :
    response jordanLinear x y z = phi x y z := by
  rw [response, phiWith, phi]
  simp [jordanLinear_apply, hilbert_inner_eq_native, quadraticWith, U]

theorem frame_radius (p : Fin 3 → Albert) (hp : Frame p) : ‖encoder p‖ ≤ Real.sqrt 2 := by
  have hs := (native_norm_sq _).trans (frame_encoder_norm p hp)
  nlinarith [ Real.sqrt_nonneg (2:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem frame_readout_lower (T : Glennie.Compact.Affine20.Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (h : ∀ x y z : Albert, ‖x‖ ≤ Real.sqrt 2 → ‖y‖ ≤ Real.sqrt 2 → ‖z‖ ≤ Real.sqrt 2 →
      |phi x y z| ≤ 38*μ*(Real.sqrt 2)^9) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have h' := (scalar_margin_lower _ _ _ (six_readout_scalar_error T noisy ε (6*ε) hreadout le_rfl)).trans
    (h _ _ _ (frame_radius _ (hT 0)) (frame_radius _ (hT 1)) (frame_radius _ (hT 2)))
  rw [show |noisyPhi noisy| = |weightedScore noisy|/2 by simp [noisyPhi, abs_div],
    show (Real.sqrt (2:ℝ))^9 = 16*Real.sqrt 2 by grind] at h'
  have hr : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ (by positivity)).2
  nlinarith

end Glennie.Compact.NativeDefectReadoutR01
