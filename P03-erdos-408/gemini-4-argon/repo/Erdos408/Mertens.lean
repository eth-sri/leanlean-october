module

public import Erdos408.Basic
public import Mathlib.NumberTheory.Bertrand
public import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# Mertens' theorems on intervals

The vendored `PrimeNumberTheoremAnd.IEANTN.Mertens` proves
`∑_{p ≤ x} log p / p = log x + O(1)` and
`∑_{p ≤ x} 1 / p = log log x + M + O(1 / log x)`. Taking differences gives
the interval forms below, which are all the prime-distribution input the
deduction needs besides Chebyshev's upper bound for `π(x)`.
-/

@[expose] public section

namespace Erdos408

open Finset Real

/-- A sum over `primesIoc y z` is the difference of the prime prefix sums up to `z`
and `y`. -/
private lemma sum_primesIoc_eq (f : ℕ → ℝ) {y z : ℝ} (hyz : y ≤ z) :
    ∑ p ∈ primesIoc y z, f p =
      ∑ p ∈ Ioc 0 ⌊z⌋₊ with p.Prime, f p - ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, f p := by
  have := sum_Ioc_consecutive (fun p ↦ if p.Prime then f p else 0) ⌊y⌋₊.zero_le
    (Nat.floor_le_floor hyz)
  simp_all [primesIoc, sum_filter]; linarith

theorem mertens_first : ∃ E : ℝ, 0 ≤ E ∧ ∀ y z : ℝ, 1 ≤ y → y ≤ z →
    |∑ p ∈ primesIoc y z, Real.log p / p - Real.log (z / y)| ≤ E := by
  obtain ⟨c, hc, hE⟩ := Mertens.E₁p.bounded
  refine ⟨2 * c, by linarith, fun y z hy hyz ↦ ?_⟩
  rw [sum_primesIoc_eq _ hyz, Mertens.sum_log_prime_div_eq, Mertens.sum_log_prime_div_eq,
    log_div (by linarith) (by linarith)]
  have := hE y hy
  have := hE z (by linarith)
  rw [abs_le] at *
  constructor <;> linarith

theorem mertens_second : ∃ E : ℝ, 0 ≤ E ∧ ∀ y z : ℝ, 2 ≤ y → y ≤ z →
    |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤
      E / Real.log y := by
  have : 0 ≤ Real.log 4 := log_nonneg (by norm_num)
  have := Mertens.E₁.nonneg
  refine ⟨2 * (Real.log 4 + 6 + Mertens.E₁), by linarith, fun y z hy hyz ↦ ?_⟩
  have hly : 0 < Real.log y := log_pos (by linarith)
  have hlyz : Real.log y ≤ Real.log z := log_le_log (by linarith) hyz
  rw [sum_primesIoc_eq _ hyz, Mertens.sum_prime_div_eq, Mertens.sum_prime_div_eq,
    log_div (by linarith) hly.ne']
  have := Mertens.E₂p.abs_le hy
  have := (Mertens.E₂p.abs_le (hy.trans hyz)).trans
    (div_le_div_of_nonneg_left (by linarith) hly hlyz)
  rw [mul_div_assoc, abs_le] at *
  constructor <;> linarith

theorem card_primesIoc_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    ((primesIoc 1 x).card : ℝ) ≤ K * x / Real.log x := by
  have : 0 ≤ Real.log 4 := log_nonneg (by norm_num)
  refine ⟨2 * Real.log 4 + 2, by linarith, fun x hx ↦ ?_⟩
  have hlx : 0 < Real.log x := log_pos (by linarith)
  have hcard : (primesIoc 1 x).card = Nat.primeCounting ⌊x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    congr 1; ext p; simp +contextual [primesIoc, Nat.primesLE, Nat.primesBelow, Nat.Prime.one_lt]
  have hpi := Chebyshev.pi_le_log4_mul_div (x := x) (by linarith)
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr (by linarith : 0 < x))
  rw [log_sqrt (by linarith)] at hpi h
  have hsqrt : √x ≤ 2 * x / Real.log x := by
    rw [le_div_iff₀ hlx]
    nlinarith [mul_self_sqrt (by linarith : 0 ≤ x)]
  rw [hcard]
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.log 4 * x / (Real.log x / 2) + √x := hpi
    _ ≤ Real.log 4 * x / (Real.log x / 2) + 2 * x / Real.log x := by gcongr
    _ = _ := by field_simp

theorem sum_log_primesIoc_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ p ∈ primesIoc 1 x, Real.log p ≤ Real.log 4 * x := by
  rw [show primesIoc 1 x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime by ext p; simp +contextual [primesIoc, Nat.Prime.pos, Nat.Prime.one_lt]]
  exact Chebyshev.theta_le_log4_mul_x hx

theorem dyadicPrimes_card_pos {x : ℝ} (hx : 1 ≤ x) : 0 < (dyadicPrimes x).card := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (Nat.floor_pos.mpr hx).ne'
  exact card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlt, hle.trans <| Nat.le_floor <| by
    push_cast; linarith [Nat.floor_le (by linarith : 0 ≤ x)]⟩, hp⟩⟩

end Erdos408
