module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedMultiplier

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

theorem reverseTimeGelfand_pairing_multiplier_eq_integral
    {d } {Ω : Set (PDE.Vec d)} {T }
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
  let G := reverseTimeGelfandCLM hΩ T u
  let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
  change reverseTimeDualPairingRightCLM hΩ T z G = _
  calc
    reverseTimeDualPairingRightCLM hΩ T z G =
        reverseTimeDualPairingCLM hΩ T G z :=
      reverseTimeDualPairingRightCLM_apply hΩ T z G
    _ = ∫ tau, G tau (z tau) ∂reverseTimeVolume T :=
      reverseTimeDualPairingCLM_apply hΩ T G z
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_reverseTimeGelfandCLM hΩ T u,
        ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hG hz
      dsimp only [G, z]
      rw [hG, hz]
      let u0 := (u tau)
      let q0 := (q tau)
      rw [scalarLpToH10HilbertGraphDual_apply, (valueCLM hΩ).map_smul,
        inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
