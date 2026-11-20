module

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.WordSwap

/-!
# Cancellation at ordinary ML edges

The product form of the coefficient identity avoids dividing by word coefficients.
Only the nonzero two-body scattering denominator is divided out.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The ML coefficient intertwines the adjacent exchange of the original
momentum labels with its Bethe scattering phase. -/
def WordWeights.Compatible {n : ℕ} (r : WordWeights n) (Δ : ℝ) (p : Fin (n+1) → ℝ) : Prop :=
  ∀ i j, Complex.exp (I * (Bethe.theta Δ (p i) (p j) : ℂ)) *
      (r.right j * r.left i - r.collision) = r.right i * r.left j - r.collision

noncomputable def wordTerm {N n : ℕ} (c : ℝ) (r : WordWeights n) (x : Fin (n+1) → ℤ)
    (p : Fin (n+1) → ℝ) (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * wordCoefficient r σ w * wordPhase (N := N) x p σ w

/-- Paired terms at an ordinary ML edge are negatives of one another. -/
theorem wordTerm_adjacent_swap {N n : ℕ} {c : ℝ} (hc : 2 < c) (r : WordWeights n)
    (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) (hr : r.Compatible (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    wordTerm (N := N) c r x p (σ * Equiv.swap a.castSucc a.succ) w =
      -wordTerm (N := N) c r x p σ w := by
  have hrot : finRotate (n+1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hswap := wordCoefficient_swap_mul r σ w ha (hrot.symm ▸ hb) _
    (hr (σ a.castSucc) (σ (finRotate (n+1) a.castSucc)))
  rw [hrot] at hswap
  unfold wordTerm
  rw [wordPhase_adjacent_swap x p σ w a ha hb,
    amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ (by simp)]
  linear_combination -amplitude (anisotropy c) p σ * wordPhase (N := N) x p σ w * hswap

/-- Every word with an ordinary ML edge contributes zero after the permutation sum. -/
theorem sum_wordTerm_eq_zero_of_adjacentML {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (r : WordWeights n) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hr : r.Compatible (anisotropy c) p)
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    (∑ σ, wordTerm (N := N) c r x p σ w) = 0 := by
  have h : (∑ σ, wordTerm (N := N) c r x p σ w) =
      ∑ σ, wordTerm (N := N) c r x p (σ * Equiv.swap a.castSucc a.succ) w :=
    (Equiv.sum_comp (Equiv.mulRight (Equiv.swap a.castSucc a.succ)) _).symm
  simp_rw [wordTerm_adjacent_swap hc r x p hr _ w a ha hb] at h
  rw [Finset.sum_neg_distrib] at h
  linear_combination (1 / 2 : ℂ) * h

end PottsDiscontinuity.BetheAnsatz
