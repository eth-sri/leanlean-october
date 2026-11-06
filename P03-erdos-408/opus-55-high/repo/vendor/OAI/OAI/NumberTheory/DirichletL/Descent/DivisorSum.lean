module

public import OAI.NumberTheory.DirichletL.Descent.DivisorExtraction

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CanonicalQuadraticSieve IdealMobiusDivisorSum
noncomputable section

def hybridDivisorPool (rows : Finset (Ideal ActualEisensteinCubic.O)) : Finset (Ideal ActualEisensteinCubic.O) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal ActualEisensteinCubic.O)) : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal ActualEisensteinCubic.O) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (by grind) hdiv,
    (QuadraticMainBoundary.norm_le_of_dvd (by grind) hdiv).trans (by grind)⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal ActualEisensteinCubic.O)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr (by grind),
      Finset.mem_biUnion.mpr (by grind)⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) K
    (by grind) (by grind)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hsum 2

end
end SevenEighths.InverseMoment

end OAI
