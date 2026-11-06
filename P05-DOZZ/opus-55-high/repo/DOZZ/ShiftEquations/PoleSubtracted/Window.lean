/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow

/-!
# The two-pole window leaves Hölder room

For the window of [KRV, (def:delta)] (`TwoPoleWindow`), put `p = 1 - 2η/γ`, the moment
threshold of the pole of charge `2/γ + η`, and `c* = (2η + δ)/γ`, the largest positive power
produced by a negative charge at the origin. The double-tail ceiling clause of the window forces
`c* < p (1 - γ²/4)`. This is exactly the room needed by the conjugate-Hölder allocation of the mixed
moments, with the full window and no shrinking of `η, δ`.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- The moment threshold of the pole of charge `2/γ + η`. -/
theorem reflectionExponent_pole {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    reflectionExponent γ (2 / γ + η) = 1 - 2 * η / γ := by
  rw [reflectionExponent, Q]
  field_simp
  ring
section
variable {γ η δ : ℝ}
section
variable (hW : TwoPoleWindow γ η δ)
include hW

theorem window_eta_pos : 0 < η := hW.1

theorem window_delta_pos : 0 < δ := hW.2.2.1

theorem window_eta_lt_quarter : η < γ / 4 :=
  lt_of_lt_of_le hW.2.1 ((min_le_right ..).trans (min_le_left ..))

end
section
variable (hγ : 0 < γ)
include hγ

theorem window_eta_le_two_div (hγ2 : γ < 2)
    (hW : TwoPoleWindow γ η δ) : η ≤ 2 / γ := by
  have h := window_eta_lt_quarter hW
  have : γ / 4 ≤ 2 / γ := by
    bound
  linarith

/-- The pole threshold `p = 1 - 2η/γ` is positive on the window. -/
theorem window_threshold_pos (hW : TwoPoleWindow γ η δ) :
    0 < 1 - 2 * η / γ := by
  have h := window_eta_lt_quarter hW
  bound

/-- **The window leaves Hölder room**: `(2η + δ)/γ < (1 - 2η/γ)(1 - γ²/4)`. -/
theorem window_holder_room (hγ2 : γ < 2)
    (hW : TwoPoleWindow γ η δ) :
    (2 * η + δ) / γ < (1 - 2 * η / γ) * (1 - γ ^ 2 / 4) := by
  have hp0 := window_threshold_pos hγ hW
  have hceil := hW.2.2.2.2.2
  set p : ℝ := 1 - 2 * η / γ with hp
  set a : ℝ := 4 / γ ^ 2 with ha
  have hrefl := reflectionExponent_pole hγ η
  have hp1 : p ≤ 1 := by
    have : 0 ≤ 2 * η / γ := div_nonneg (by linarith [window_eta_pos hW]) hγ.le
    linarith
  have ha1 : 1 < a := by
    rw [ha, lt_div_iff₀ (by positivity)]
    nlinarith
  have hMc : oneInsertionMomentCeiling γ (2 / γ + η) ≤ a := by
    rw [oneInsertionMomentCeiling]
    simp_all
  have hMc0 : 0 ≤ oneInsertionMomentCeiling γ (2 / γ + η) := by
    rw [oneInsertionMomentCeiling, hrefl]
    positivity
  have herr : oneInsertionErrorCeiling γ (2 / γ + η) ≤ (a - p) / (1 + a) := by
    rw [oneInsertionErrorCeiling, hrefl, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hceil' : twoInsertionTailCeiling γ (2 / γ + η) (Q γ - η - γ / 2) ≤
      p + (a - p) / (1 + a) := by
    rw [twoInsertionTailCeiling]
    refine (min_le_left ..).trans ?_
    rw [hrefl, twoInsertionPointLoss]
    have := min_le_left (oneInsertionErrorCeiling γ (2 / γ + η))
      (min ((Q γ - (Q γ - η - γ / 2)) / γ) (1 / 2))
    linarith
  have hid : p + (a - p) / (1 + a) - 1 = (p * a - 1) / (1 + a) := by
    field_simp
    ring
  have hc : (2 * η + δ) / γ < (p * a - 1) / (1 + a) := by linarith
  refine hc.trans_le ?_
  have hγa : γ ^ 2 / 4 = 1 / a := by
    rw [ha]
    field_simp
  rw [hγa, div_le_iff₀ (by linarith)]
  have hexp : p * (1 - 1 / a) * (1 + a) = p * a - p / a := by
    field_simp
    ring
  rw [hexp]
  have : p / a ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith

end

end

end DOZZ.Proofs

end
