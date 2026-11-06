module
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by grind

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

end
end SevenEighths.CubicSieve

end OAI
