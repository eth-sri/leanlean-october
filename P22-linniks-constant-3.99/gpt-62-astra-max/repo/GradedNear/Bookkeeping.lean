module

public import GradedNear.Defs

/-!
# Gram bookkeeping

If `M_{jk} ≤ R_{jk} + ε` on pairs of the same class and `M_{jk} ≤ d + ε` otherwise, with `R`
symmetric and `a ≥ 0`, then
`Σ_{j,k} a_j a_k M_{jk} ≤ Σ_j (R_{jj} - d + Σ_{k ≠ j, same} (R_{jk} - d)_+) a_j² + (d + ε)(Σ a)²`.
The pair excess uses `2 a_j a_k ≤ a_j² + a_k²` (paper §8.5).
-/

@[expose] public section

namespace GradedNear

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gram_bookkeeping {α : Type*} (χ : ι → α)
    (M R : ι → ι → ℝ) (hR : ∀ j k, R j k = R k j) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (d ε : ℝ)
    (hsame : ∀ j k, χ j = χ k → M j k ≤ R j k + ε) (hdiff : ∀ j k, χ j ≠ χ k → M j k ≤ d + ε) :
    ∑ j, ∑ k, a j * a k * M j k ≤
      ∑ j, (R j j - d + ∑ k ∈ sameCharOthers χ j, max 0 (R j k - d)) *
          a j ^ 2 + (d + ε) * (∑ j, a j) ^ 2 := by
  classical
  let P j k := if k = j then R j j-d else if χ k = χ j then max 0 (R j k-d) else 0
  let charge j k := P j k * a j^2
  have hp j k : a j*a k*M j k ≤ (charge j k + charge k j)/2 + a j*a k*(d+ε) := by
    have hnn := mul_nonneg (ha j) (ha k)
    by_cases h : k = j
    · subst k; simp [charge,P]; grw [hsame j j rfl]; linarith only
    · by_cases hs : χ k = χ j
      · simp [charge,P,h,Ne.symm h,hs,hR k j]
        nlinarith only [mul_le_mul_of_nonneg_left (hsame j k hs.symm) hnn,
          mul_le_mul_of_nonneg_left (le_max_right 0 (R j k-d)) hnn,
          mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a j) (a k)) (le_max_left 0 (R j k-d))]
      · simpa [charge,P,h,Ne.symm h,hs,Ne.symm hs] using
          mul_le_mul_of_nonneg_left (hdiff j k (Ne.symm hs)) hnn
  have swap : ∑ j, ∑ k, charge k j = ∑ j, ∑ k, charge j k := sum_comm
  have htotal j : ∑ k, charge j k = (R j j - d + ∑ k ∈ sameCharOthers χ j, max 0 (R j k-d)) * a j^2 := by
    dsimp [charge]; rw [← sum_mul]; 
    simp [P, sameCharOthers, sum_ite, filter_filter, show univ.filter (· = j) = {j} by ext; simp]
  grw [hp]
  simp_rw [sum_add_distrib, ← sum_div, sum_add_distrib, swap, add_self_div_two, htotal,
    ← sum_mul, ← sum_mul_sum, sq]
  rw [mul_comm (d+ε), mul_add]

end GradedNear
