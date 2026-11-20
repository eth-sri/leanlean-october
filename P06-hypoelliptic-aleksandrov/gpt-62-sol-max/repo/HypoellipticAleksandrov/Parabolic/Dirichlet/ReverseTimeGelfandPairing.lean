module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedTest

/-!
# Reverse-time Gelfand pairings

This module rewrites the pivot Gelfand pairing against a separated bounded
scalar multiplier as the literal spatial `L²` mass integral.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Pairing the Gelfand image with a bounded separated multiplier is the
literal spatial `L²` mass integral. -/
theorem reverseTimeGelfand_pairing_multiplier_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ T)
    (q : ℝ → ℝ)
    (hq : MeasureTheory.MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeGelfandCLM hΩ T u) =
      ∫ tau,
        inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * q tau
        ∂reverseTimeVolume T := by
  refine reverseTimeDualPairing_multiplier_eq_integral hΩ _ q hq v ?_
  filter_upwards [coeFn_reverseTimeGelfandCLM hΩ T u] with t ht
  rw [ht, scalarLpToH10HilbertGraphDual_apply]

end HypoellipticAleksandrov.Parabolic.Dirichlet
