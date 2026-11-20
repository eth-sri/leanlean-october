module

public import PottsDiscontinuity.Torus.LoopTurnDivisibility
public import PottsDiscontinuity.Torus.LoopTurnOrientation

/-! # Integer rotation numbers of the smoothed torus loops

The port-angle cocycle makes the total signed turn an integer multiple of one full
turn. This module records the resulting integer without claiming its homological
classification.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- The integer number of full rotations of a directed loop. -/
noncomputable def loopRotationNumber {ω : ArrowConfig N M} {s : Smoothing N M}
    {h : CompatibleConfig ω s} (q : DirectedLoop h) : ℤ :=
  loopTurn q / 4

variable (ω₀ ω₁ : ArrowConfig N M) (ω : ArrowConfig N M) (s : Smoothing N M)
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (q : DirectedLoop h₀)

/-- The total quarter-turn count is exactly four times its rotation number. -/
theorem loopTurn_eq_four_mul_rotationNumber
    (h : CompatibleConfig ω s) (q : DirectedLoop h) :
    loopTurn q = 4 * loopRotationNumber q := by
  have hz := loopTurn_mod_four ω s h q
  have hd : (4 : ℤ) ∣ loopTurn q := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  grind [loopRotationNumber]

/-- Reorienting a loop changes the sign of its integer rotation number when the
arrow orientation is reversed. -/
theorem loopRotationNumber_reorient :
    loopRotationNumber (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ h₁ q then loopRotationNumber q
      else -loopRotationNumber q := by
  unfold loopRotationNumber
  rw [loopTurn_reorient]
  split_ifs with hor
  · rfl
  · have ht := loopTurn_eq_four_mul_rotationNumber ω₀ s h₀ q
    grind

end PottsDiscontinuity.Torus
