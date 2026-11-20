module

public import GradedNear.SieveBasic

/-!
# The Selberg majorant of `Λ` and the small prime powers

For a prime above the sieve level only the divisor `1` contributes, so the Selberg square is
exactly `1`. The total `Λ(n)/n` mass at non-primes is finite, by the summability of the
non-prime terms in Dirichlet's theorem (take the single residue class modulo one).
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

noncomputable abbrev pp (n : ℕ) := if n.Prime then 0 else Λ n
noncomputable def ppMass := ∑' n : ℕ, pp n / n

lemma pp_nonneg (n : ℕ) : 0 ≤ pp n := by unfold pp; split <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

lemma pp_le_mass (C : Finset ℕ) : ∑ n ∈ C, pp n / n ≤ ppMass := by
  have hz (n : ℕ) : (n : ZMod 1) = 0 := Subsingleton.elim ..
  have h : Summable fun n : ℕ => pp n / n := by
    simpa [pp, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, hz] using
      ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  exact h.sum_le_tsum C fun n _ => div_nonneg (pp_nonneg n) (Nat.cast_nonneg _)

lemma vonMangoldt_le_sieve {V : ℝ} (hV : 1 < V) {n : ℕ} (hn : V < n) :
    Λ n ≤ Real.log n * sieveNu V n + pp n := by
  by_cases hp : n.Prime
  · simp [pp, hp, hp.divisors, Ne.symm hp.ne_one, grahamWeight, hV.le,
      hn.not_ge, (Real.log_pos hV).ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simpa [pp, hp] using mul_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)

end GradedNear
