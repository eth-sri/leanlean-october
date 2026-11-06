import Mathlib.Tactic

import GS.MatrixFactor.OrdinaryQR
import GS.MatrixFactor.Permutations



/-! Support recovery for the actual complex triangular Gram factor. This
proves support of the unitary factor obtained from ordinary complex QR. -/
open Matrix GS.MatrixBase
namespace GS.MatrixFactor
variable {𝕜 : Type} [RCLike 𝕜]
/-- A triangular Gram factor cannot connect two distinct block labels if its
Gram matrix has no such connections. This is a scalar induction, NOT a claim
that every zero in a Gram matrix is preserved by Cholesky. -/
 theorem upper_supported_of_gram {block : Fin n → ℕ} {R : KMat 𝕜 n}
    (ht : CUpper R) (hd : ∀ i, R i i ≠ 0)
    (hg : CSupported block (Rᴴ*R)) : CSupported block R := by
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
    intro j hij
    have hsum : (Rᴴ*R) i j = star (R i i) * R i j := by
      rw [Matrix.mul_apply]
      change (∑ k : Fin n, star (R k i) * R k j) = star (R i i) * R i j
      apply Finset.sum_eq_single i
      · intro k hk hki
        by_cases hlt : k.val < i.val
        · by_cases hbi : block k = block i
          · aesop
          · aesop
        · have hgt : i.val < k.val := by
            omega
          rw [ht hgt, star_zero, zero_mul]
      · aesop
    have he := hsum.symm.trans (hg i j hij)
    exact (mul_eq_zero.mp he).resolve_left (by aesop)

end GS.MatrixFactor
