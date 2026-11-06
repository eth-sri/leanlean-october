module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalGeometry

/-!
# Discharge of the transported-radius condition for terminal comparison

Compact terminal support supplies the transported bound Z. Any positive collar margin
then supplies a threshold R0 beyond which the actual ellipsoids contain that support
throughout the common terminal window.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/- A compact terminal support has a uniform Euclidean transported-coordinate bound. -/
theorem exists_transportedRadius_terminal_window {r d } (hr : 0 < r) (hd : 0 < d)
    (hdr : d < r) (Z : ℝ) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
      (r - d) ^ 2 / r ^ 2 + Z ^ 2 / R ^ 2 < 1 := by
  have hsq : (r - d) ^ 2 < r ^ 2 := by nlinarith
  have hfrac : (r - d) ^ 2 / r ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hr)).mpr hsq
  let η := 1 - (r - d) ^ 2 / r ^ 2
  have hη : 0 < η := sub_pos.mpr hfrac
  let R0 := 1 + (Z ^ 2 + 1) / η
  have hR01 : 1 < R0 := by
    change 1 < 1 + (Z ^ 2 + 1) / η
    have : 0 < (Z ^ 2 + 1) / η := div_pos (by positivity) hη
    linarith
  refine ⟨R0, by linarith, fun R hR => ?_⟩
  have hR1 := hR01.le.trans hR
  have hRsq : R0 ≤ R ^ 2 := by nlinarith
  have he : η * R0 = η + (Z ^ 2 + 1) := by
    dsimp only [R0]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hη.ne']
  have hz : Z ^ 2 < η * R ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hRsq hη.le
    linarith
  have hf : Z ^ 2 / R ^ 2 < η := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  dsimp only [η] at hf
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
