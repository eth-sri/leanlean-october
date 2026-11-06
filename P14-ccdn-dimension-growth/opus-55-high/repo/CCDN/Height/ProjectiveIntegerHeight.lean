/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveAffineChart

/-! Integral representatives need not be primitive to provide an upper
bound on projective height. Removing their gcd can only decrease the
maximum absolute coordinate. -/

namespace CCDN
section

variable {n : ℕ}

/-- A nonzero integer vector with all coordinates of absolute value at most `B` spans a projective
point of height at most `B`, whether or not its coordinates are coprime. -/
theorem projective_integer_height_le (z : IntPoint (n + 1)) (hz : z ≠ 0)
    {B : ℝ} (hbox : InBox z B) :
    (Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz)).mulHeight ≤ B := by
  obtain ⟨v, hv, hprim⟩ := Finset.extract_gcd z
    (show (Finset.univ : Finset (Fin (n + 1))).Nonempty from Finset.univ_nonempty)
  have he (j : Fin (n + 1)) : z j = Finset.univ.gcd z * v j := hv j (Finset.mem_univ j)
  have hv0 : v ≠ 0 := by
    intro h
    apply hz
    funext j
    simp_all
  have hg1 : (1 : ℝ) ≤ |((Finset.univ.gcd z : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (by
      intro h
      apply hz
      funext j
      simp_all)
  have hvbox : InBox v B := by
    intro j
    have hh := hbox j
    rw [he j, Int.cast_mul, abs_mul] at hh
    nlinarith [abs_nonneg (v j : ℝ)]
  have hproj : Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz) =
      Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0) := by
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
    refine ⟨((Finset.univ.gcd z : ℤ) : ℚ), ?_⟩
    funext j
    change ((Finset.univ.gcd z : ℤ) : ℚ) * (v j : ℚ) = (z j : ℚ)
    rw [he j, Int.cast_mul]
  rw [hproj, projective_height_primitive v hv0 hprim]
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j => |v j|)
  have hmax : (⨆ j, |v j| : ℤ) = |v j| := by
    apply le_antisymm
    · exact ciSup_le hj
    · exact le_ciSup (Finite.bddAbove_range (fun k => |v k|)) j
  rw [hmax, Int.cast_abs]
  exact hvbox j

