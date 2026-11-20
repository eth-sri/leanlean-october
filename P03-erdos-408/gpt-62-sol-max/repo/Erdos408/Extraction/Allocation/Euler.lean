module

public import Erdos408.Extraction.Allocation.Groups
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Reciprocal sums over factored numbers

Elementary Euler-product bounds used for the mean square of the core.

* The reciprocals of the `S`-factored numbers in a finite set sum to at most
  `∏_{p ∈ S} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ S} 1/p)`.
-/

@[expose] public section

namespace Erdos408

open Finset Real

/-- The reciprocals of finitely many `S`-factored numbers sum to at most
`∏_{p ∈ S} (1 - 1/p)⁻¹`. -/
lemma sum_inv_le_prod_of_factored (S : Finset ℕ) (F : Finset ℕ)
    (hF : ∀ n ∈ F, n ∈ Nat.factoredNumbers S) :
    ∑ n ∈ F, (1 : ℝ) / n ≤ ∏ p ∈ S with p.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  -- the Euler product for `n ↦ 1/n`
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → (1 : ℝ) / (m * n : ℕ) = 1 / m * (1 / n) := by
    intro m n _
    push_cast
    rw [one_div_mul_one_div]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun n : ℕ => ‖(1 : ℝ) / (p ^ n : ℕ)‖ := by
    intro p hp
    have h1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    refine (summable_geometric_of_lt_one (by positivity) h1).congr fun n => ?_
    rw [norm_of_nonneg (by positivity)]
    push_cast
    rw [one_div_pow]
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1 : ℝ) / n) (by simp) hmul hsum S
  have hgeom : ∀ p ∈ S.filter Nat.Prime, ∑' n : ℕ, (1 : ℝ) / (p ^ n : ℕ) = (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp := (mem_filter.1 hp).2
    have h1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    rw [← tsum_geometric_of_lt_one (by positivity) h1]
    exact tsum_congr fun n => by push_cast; rw [one_div_pow]
  rw [prod_congr rfl hgeom] at hhas
  have hle := sum_le_hasSum (F.subtype (· ∈ Nat.factoredNumbers S))
    (fun i _ => by positivity) hhas
  rw [Finset.sum_subtype_eq_sum_filter (f := fun n : ℕ => (1 : ℝ) / n),
    filter_true_of_mem hF] at hle
  exact hle

/-- `(1 - 1/p)⁻¹ ≤ exp(2/p)` for `p ≥ 2`. -/
lemma inv_one_sub_le_exp {p : ℝ} (hp : 2 ≤ p) : (1 - 1 / p)⁻¹ ≤ Real.exp (2 / p) := by
  have ht  := one_div_le_one_div_of_le (by norm_num) hp
  have ht0 : 0 < 1 / p := by positivity
  rw [inv_le_comm₀ (by linarith) (exp_pos _), ← exp_neg]
  -- `exp(-2t) ≤ 1 / (1 + 2t) ≤ 1 - t` for `0 ≤ t ≤ 1/2`
  have h1 : Real.exp (-(2 / p)) ≤ 1 / (1 + 2 / p) := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [add_one_le_exp (2 / p)])
  have h2 : 1 / (1 + 2 / p) ≤ 1 - 1 / p := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 / p = 2 * (1 / p) := by ring
    rw [this]
    nlinarith
  linarith

/-- `∏_{p ∈ S} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ S} 1/p)` over primes. -/
lemma prod_inv_one_sub_le_exp (S : Finset ℕ) :
    ∏ p ∈ S with p.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (2 * ∑ p ∈ S with p.Prime, (1 : ℝ) / p) := by
  rw [mul_sum, exp_sum]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    exact (inv_pos.2 (by linarith)).le
  · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    rw [mul_one_div]
    exact inv_one_sub_le_exp h2

end Erdos408
