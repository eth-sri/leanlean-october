module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Choosing a structural Hölder exponent

Continuity at exponent zero supplies an exponent below one. The real power identities
then convert the dyadic geometric envelope into a power of the physical distance.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

/- Every contraction factor admits a strictly positive Hölder exponent below one. -/
theorem geometric_decay_le_holder_power {q α x : ℝ}
    (hq : 0 ≤ q) (hα : 0 < α) (hqx : q ≤ (1 / 2 : ℝ) ^ α)
    (n : ℕ) (hn : (1 / 2 : ℝ) ^ (n + 1) < x) :
    q ^ n ≤ (2 * x) ^ α := by
  have hpow : (1 / 2 : ℝ) ^ n < 2 * x := by
    rw [pow_succ] at hn
    linarith only [hn]
  calc q ^ n ≤ ((1 / 2 : ℝ) ^ α) ^ n := pow_le_pow_left₀ hq hqx n
    _ = ((1 / 2 : ℝ) ^ n) ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm α (n : ℝ)]
    _ ≤ (2 * x) ^ α := Real.rpow_le_rpow (pow_nonneg (by norm_num) n) hpow.le hα.le

end HypoellipticAleksandrov.Parabolic.LocalHolder
