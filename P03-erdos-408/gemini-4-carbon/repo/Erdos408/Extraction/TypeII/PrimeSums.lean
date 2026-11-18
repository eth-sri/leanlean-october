module

public import Erdos408.Mertens
public import Erdos408.Extraction.Defs

/-!
# Prime sums for the proxy estimates

Mertens' third theorem in the form `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`, and the
identification of the prime sets `primesIcc 2 y`, `primesIoc 1 y` and
`{p ≤ N prime}` used by the Euler-product bounds.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

theorem mem_primesIcc {a b : ℝ} {p : ℕ} :
    p ∈ primesIcc a b ↔ p.Prime ∧ ⌈a⌉₊ ≤ p ∧ p ≤ ⌊b⌋₊ := by
  simp only [primesIcc, mem_filter, mem_Icc]
  tauto


/-- Mertens' third theorem, lower bound: `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`. -/
theorem mertens_third_lower : ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ y : ℝ, 2 ≤ y →
    c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p) := by
  obtain ⟨E, hE, hsum⟩ := abs_sum_inv_primes_sub_le
  refine ⟨Real.exp (-(E + 4)), Real.exp_pos _, fun y hy => ?_⟩
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hset : primesIcc 2 y = primesIoc 1 y := by
    ext p
    simp only [primesIcc, mem_filter, mem_Icc, mem_primesIoc, show ⌈(2 : ℝ)⌉₊ = 2 by norm_num]
    exact ⟨fun ⟨⟨_, hp⟩, hpr⟩ => ⟨hpr, by exact_mod_cast hpr.one_lt,
      (Nat.le_floor_iff (by linarith)).mp hp⟩,
      fun ⟨hpr, _, hp⟩ => ⟨⟨hpr.two_le, Nat.le_floor hp⟩, hpr⟩⟩
  rw [hset]
  have hpt : ∀ p ∈ primesIoc 1 y,
      Real.exp (-((1 : ℝ) / p + 2 / (p : ℝ) ^ 2)) ≤ 1 - (1 : ℝ) / p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.mp hp).1.two_le
    set u : ℝ := (1 : ℝ) / p
    have hu0 : 0 ≤ u := by positivity
    have hu2 : u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have hpoly : 1 ≤ (1 - u) * (1 + u + 2 * u ^ 2) := by nlinarith
    have hexp : 1 + u + 2 * u ^ 2 ≤ Real.exp (u + 2 * u ^ 2) := by
      linarith [Real.add_one_le_exp (u + 2 * u ^ 2)]
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _),
      show 2 / (p : ℝ) ^ 2 = 2 * u ^ 2 by dsimp [u]; ring]
    exact hpoly.trans (mul_le_mul_of_nonneg_left hexp (by linarith))
  have hsq : ∑ p ∈ primesIoc 1 y, 2 / (p : ℝ) ^ 2 ≤ 4 := by
    calc ∑ p ∈ primesIoc 1 y, 2 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ primesIoc 1 y, 2 * (1 / ((p : ℝ) * √(p : ℝ))) := by
          refine sum_le_sum fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.mp hp).1.two_le
          have hsp : √(p : ℝ) ≤ p := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ p by linarith), Real.sqrt_nonneg p]
          rw [sq, mul_one_div]
          exact div_le_div_of_nonneg_left (by norm_num)
            (mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith)))
            (mul_le_mul_of_nonneg_left hsp (by linarith))
      _ ≤ ∑ p ∈ Icc 2 ⌊y⌋₊, 2 * (1 / ((p : ℝ) * √(p : ℝ))) := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
          obtain ⟨hpr, _, hpy⟩ := mem_primesIoc.mp hp
          exact mem_Icc.mpr ⟨hpr.two_le, Nat.le_floor hpy⟩
      _ = 2 * ∑ p ∈ Icc 2 ⌊y⌋₊, 1 / ((p : ℝ) * √(p : ℝ)) := (mul_sum ..).symm
      _ ≤ 4 := by linarith [sum_inv_mul_sqrt_le ⌊y⌋₊]
  have hm := (abs_le.mp (hsum y hy)).2
  calc Real.exp (-(E + 4)) / Real.log y
      = Real.exp (-(Real.log (Real.log y) + E + 4)) := by
        rw [show -(Real.log (Real.log y) + E + 4) = -(E + 4) - Real.log (Real.log y) by ring,
          Real.exp_sub, Real.exp_log hly]
    _ ≤ Real.exp (-∑ p ∈ primesIoc 1 y, ((1 : ℝ) / p + 2 / (p : ℝ) ^ 2)) := by
        rw [sum_add_distrib]; exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ ∏ p ∈ primesIoc 1 y, (1 - (1 : ℝ) / p) := by
        rw [← sum_neg_distrib, Real.exp_sum]
        exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) hpt

end Erdos408.TypeII
