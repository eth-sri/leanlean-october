/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveAffineChart

/-! Integral representatives need not be primitive to provide an upper
bound on projective height. Removing their gcd can only decrease the
maximum absolute coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A nonzero integer vector with all coordinates of absolute value at most `B` spans a projective
point of height at most `B`, whether or not its coordinates are coprime. -/
theorem projective_integer_height_le {n : ℕ} (z : IntPoint (n + 1)) (hz : z ≠ 0)
    {B : ℝ} (hbox : InBox z B) :
    (Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz)).mulHeight ≤ B := by
  let p := Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz)
  let v := primitiveProjectiveRep p
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp (primitiveProjectiveRep_mk p).symm
  obtain ⟨k, hk⟩ := integral_scalar_of_primitive (primitiveProjectiveRep_gcd p) hc.symm
  have hk0 : k ≠ 0 := by exact_mod_cast (hk.trans_ne c.ne_zero)
  obtain ⟨j, hj⟩ := primitiveProjectiveRep_height_eq p
  have he : (z j : ℤ) = k * v j := by
    have hq : (c : ℚ) * (v j : ℚ) = z j := congrFun hc j
    rw [← hk] at hq
    exact_mod_cast hq.symm
  have h := hbox j
  rw [he, Int.cast_mul, abs_mul, hj] at h
  exact (le_mul_of_one_le_left p.mulHeight_pos.le (by exact_mod_cast Int.one_le_abs hk0)).trans h

end
end CCDN
