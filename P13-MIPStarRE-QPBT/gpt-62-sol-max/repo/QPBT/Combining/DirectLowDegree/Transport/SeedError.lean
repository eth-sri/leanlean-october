module

public import QPBT.Combining.DirectLowDegree.Transport.Error
public import QPBT.Games.ErrorFunctions

/-!
# Error absorption for seed compression

The recovery of global polynomial consistency after seed compression costs a
square root of the direct soundness error. Halving its exponent preserves the
error function of blueprint `lem:ld-soundness`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
-/

@[expose] public section

namespace MIPStarRE.QPBT

private abbrev DirectLdParams.seedSize (D : DirectLdParams) : ℝ := ((D.d * D.m * D.k : ℕ) : ℝ)

private theorem DirectLdParams.seedSize_ge_one (D : DirectLdParams) : 1 ≤ D.seedSize :=
  Nat.one_le_cast.mpr (Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)

section

variable (D : DirectLdParams) {a b ε : ℝ}
    (ha : 1 ≤ a)
include D a b ε ha

/-- The square-root loss from seed compression is absorbed by enlarging the
universal prefactor and halving the error exponent in `lem:ld-soundness`. -/
theorem ten_sqrt_deltaLd_le (hε : 0 ≤ ε) :
    10 * Real.sqrt (deltaLd a b ε D.q D.m D.d D.k) ≤
      deltaLd (10 * a) (b / 2) ε D.q D.m D.d D.k := by
  have h := rpow_soundnessEnvelope_le D.q (D.m * D.d : ℕ) b
    (D.seedSize_ge_one.trans (size_le_power_prefactor D.seedSize_ge_one ha)) hε
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [Real.sqrt_eq_rpow, show b / 2 = b * (1 / 2) by ring]
  change 10 * (a * D.seedSize ^ a * soundnessTail D.q (D.m * D.d : ℕ) b ε) ^ (1 / 2 : ℝ) ≤
    10 * a * D.seedSize ^ (10 * a) * soundnessTail D.q (D.m * D.d : ℕ) (b * (1 / 2)) ε
  refine (mul_le_mul_of_nonneg_left h (by norm_num)).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (soundnessTail_nonneg D.q _ _ hε)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le D.seedSize_ge_one (by linarith)) (by linarith)

/-- For errors at most one, `deltaLd` dominates the rejection probability and
 the polynomial collision probability needed after seed compression. -/
theorem error_and_collision_le_deltaLd (hb : b ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaLd a b ε D.q D.m D.d D.k ∧
      (D.m : ℝ) * D.d / D.q ≤ deltaLd a b ε D.q D.m D.d D.k := by
  let n : ℝ := (D.m * D.d : ℕ)
  have hC := size_le_power_prefactor D.seedSize_ge_one ha
  have hq : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have hc : (D.m : ℝ) * D.d ≤ D.seedSize := by
    have hk : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk
    simp only [DirectLdParams.seedSize, Nat.cast_mul]
    grw [← hk, mul_one, mul_comm (D.d : ℝ)]
  simp only [div_eq_mul_inv]
  refine ⟨?_, ?_⟩
  · have he : ε ≤ ε ^ b := by simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 hb
    exact he.trans ((rpow_noise_le_soundnessTail D.q n b ε).trans
      (le_mul_of_one_le_left (soundnessTail_nonneg D.q n b hε.le) (D.seedSize_ge_one.trans hC)))
  · have hq' : (D.q : ℝ)⁻¹ ≤ (D.q : ℝ) ^ (-b) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hb)
    exact mul_le_mul (hc.trans hC) (hq'.trans (rpow_field_le_soundnessTail D.q n b hε.le))
      (by positivity) (zero_le_one.trans (D.seedSize_ge_one.trans hC))

end

end MIPStarRE.QPBT
