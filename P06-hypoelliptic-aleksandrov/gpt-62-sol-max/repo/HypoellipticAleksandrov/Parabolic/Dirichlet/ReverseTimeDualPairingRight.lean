module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedTest

/-!
# Right reverse-time dual pairings

This module normalizes evaluation of the reverse-time dual pairing at a fixed
primal `L²(V)` test.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (z : ReverseTimeL2V hΩ T)
include z

/-- The reverse-time dual pairing evaluated at a fixed primal test on the right. -/
noncomputable def reverseTimeDualPairingRightCLM : ReverseTimeL2VStar hΩ T →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ z).comp (reverseTimeDualPairingCLM hΩ T)

/-- Right evaluation of `reverseTimeDualPairingRightCLM`. -/
@[simp] theorem reverseTimeDualPairingRightCLM_apply (g : ReverseTimeL2VStar hΩ T) :
    reverseTimeDualPairingRightCLM hΩ T z g =
      reverseTimeDualPairingCLM hΩ T g z := rfl

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hΩ : IsOpen Ω) (g : ReverseTimeL2VStar hΩ T)
  (q : ℝ → ℝ) (hq : MemLp q ∞ (reverseTimeVolume T)) (v : H10HilbertGraph hΩ) {f : ℝ → ℝ}
  (hf : ∀ᵐ t ∂reverseTimeVolume T, g t v = f t)
include hf

/-- Evaluate a reverse-time dual slice against a bounded separated multiplier. -/
theorem ae_reverseTimeDualPairing_multiplier :
    (fun t => g t (reverseTimeSeparatedVTestOfMemLp hΩ q hq v t)) =ᵐ[reverseTimeVolume T]
      fun t => f t * q t := by
  filter_upwards [ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v, hf] with t ht hv
  rw [ht, ContinuousLinearMap.map_smul, smul_eq_mul, hv, mul_comm]

/-- A separated dual pairing is the scalar integral of the pointwise evaluation. -/
theorem reverseTimeDualPairing_multiplier_eq_integral :
    reverseTimeDualPairingRightCLM hΩ T (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) g =
      ∫ t, f t * q t ∂reverseTimeVolume T := by
  rw [reverseTimeDualPairingRightCLM_apply, reverseTimeDualPairingCLM_apply]
  exact integral_congr_ae (ae_reverseTimeDualPairing_multiplier hΩ g q hq v hf)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
