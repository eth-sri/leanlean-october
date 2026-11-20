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

/-- The primes up to `y ≥ 0` are `primesIcc 2 y`. -/
theorem primesIcc_two_eq (y : ℝ) : primesIcc 2 y = (Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  rw [mem_primesIcc, mem_filter, mem_Ioc]
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
  rw [h2]
  constructor
  · rintro ⟨hp, -, h⟩
    exact ⟨⟨hp.pos, h⟩, hp⟩
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, hp.two_le, h⟩

/-- Mertens' third theorem, lower bound: `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`. -/
theorem mertens_third_lower : ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ y : ℝ, 2 ≤ y →
    c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p) := by
  obtain ⟨C, hC⟩ := Mertens.E₃.abs_le
  refine ⟨Real.exp (-eulerMascheroniConstant) * Real.exp (-(|C| / Real.log 2)), by positivity,
    fun y hy => ?_⟩
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : 0 < Real.log y := lt_of_lt_of_le hl2 hly
  rw [primesIcc_two_eq, Mertens.prod_one_minus_div_prime_eq (by linarith)]
  have hE := hC y hy
  have hE' : -(|C| / Real.log 2) ≤ Mertens.E₃ y := by
    have h1 : C / Real.log y ≤ |C| / Real.log 2 := by
      calc C / Real.log y ≤ |C| / Real.log y := by gcongr; exact le_abs_self C
        _ ≤ |C| / Real.log 2 := div_le_div_of_nonneg_left (abs_nonneg C) hl2 hly
    have := neg_abs_le (Mertens.E₃ y)
    rw [abs_le] at hE
    linarith
  gcongr

end Erdos408.TypeII
