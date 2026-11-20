module
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.Compact.NearbyOrbitsClosed
public import Glennie.Theorems.Frames
@[expose] public section
namespace Glennie.Compact.NativeDefectReadoutR01
open Glennie
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

@[simp] theorem native_response_eq (x y z : Albert) :
    response jordanLinear x y z = phi x y z := by
  rw [response, phiWith, phi]
  simp only [jordanLinear_apply, hilbert_inner_eq_native, quadraticWith, U]

/-- Product defect bounds the native response whenever the target response vanishes. -/
theorem native_defect_response {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (j : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hJ : ∀ a b, ‖j a b‖ ≤ ‖a‖ * ‖b‖) (hU : ∀ a b, ‖Q j a b‖ ≤ ‖a‖^2 * ‖b‖)
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b, ‖f (jordan a b) - j (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hzero : response j (f x) (f y) (f z) = 0) : |phi x y z| ≤ 38 * μ * R^9 := by
  simpa only [native_response_eq, hzero, sub_zero] using
    response_discrepancy_radius jordanLinear j f jordan_norm hJ U_norm hU μ hμ hdef R hR
      x y z hx hy hz

private theorem frame_radius (p : Fin 3 → Albert) (hp : Frame p) :
    ‖encoder p‖ ≤ Real.sqrt 2 := by
  rw [← Real.sqrt_sq (norm_nonneg (encoder p)), native_norm_sq, frame_encoder_norm p hp]

/-- Turn a response bound at the frame radius into a measured defect bound. -/
theorem frame_noisy_defect_lower (T : Affine20.Triple) (hT : IsFrameTriple T)
    (noisy : Readouts) (ε μ : ℝ) (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hresponse : ∀ x y z : Albert, ‖x‖ ≤ Real.sqrt 2 → ‖y‖ ≤ Real.sqrt 2 → ‖z‖ ≤ Real.sqrt 2 →
      |phi x y z| ≤ 38 * μ * (Real.sqrt 2)^9) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  have he := phi_error T noisy ε hreadout
  have hb := hresponse _ _ _ (frame_radius _ (hT 0)) (frame_radius _ (hT 1)) (frame_radius _ (hT 2))
  have h := abs_sub_abs_le_abs_sub (noisyPhi noisy) (Sections.phiOf T)
  have hp : (Real.sqrt 2)^9 = 16 * Real.sqrt 2 := by
    rw [show (9 : ℕ) = 2 * 4 + 1 by decide, pow_succ, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hp] at hb
  simp only [noisyPhi, abs_div] at h he
  apply (div_le_iff₀ (by positivity : 0 < 1216 * Real.sqrt (2 : ℝ))).2
  change |Sections.phiOf T| ≤ _ at hb
  linarith

end
end Glennie.Compact.NativeDefectReadoutR01
