module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of reverse-time dual pairings

This module proves the `L¹` integrability of the pointwise pairing of the
reverse-time `L²(V*)` and `L²(V)` Bochner representatives.
-/

 public section

open MeasureTheory Set
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The literal pointwise dual pairing of reverse-time `L²(V*)` and `L²(V)`
curves is integrable on the reverse-time volume. -/
theorem integrable_reverseTimeDualPairing
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    MeasureTheory.Integrable (fun tau => (g tau) (u tau))
      (reverseTimeVolume T) := (memLp_one_iff_integrable.mp
  (ContinuousLinearMap.memLp_of_bilin 1 (ContinuousLinearMap.apply ℝ ℝ).flip (Lp.memLp g) (Lp.memLp u)))

end HypoellipticAleksandrov.Parabolic.Dirichlet
