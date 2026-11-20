module

public import PottsDiscontinuity.BetheAnsatz.WordCoefficients

/-!
# Swapping the two momenta at an ML edge

Only one edge coefficient changes: the two momenta occur nowhere else in rσ(w).
This algebraic identity does not require Bethe equations or division by coefficients.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section

variable {n : ℕ} (r : WordWeights n)
  (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool)

/-- Every edge other than the chosen ML edge ignores the two swapped momenta. -/
theorem wordEdgeFactor_swap_of_ne
    {a k : Fin (n + 1)} (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hk : k ≠ a) :
    wordEdgeFactor r (σ * Equiv.swap a (finRotate (n + 1) a)) w k =
      wordEdgeFactor r σ w k := by
  let b := finRotate (n + 1) a
  have hnext := fun he => hk ((finRotate _).injective he)
  unfold wordEdgeFactor
  simp only [Equiv.Perm.mul_apply]
  by_cases hkb : k = b
  · subst k
    simp only [show w b = true from hb, ↓reduceIte]
    by_cases hna : finRotate (n + 1) b = a
    · simp only [hna, ha, Bool.false_eq_true, ↓reduceIte]
    · rw [Equiv.swap_apply_of_ne_of_ne hna hnext]
  · have hswap : Equiv.swap a b k = k := Equiv.swap_apply_of_ne_of_ne hk hkb
    rw [hswap]
    by_cases hna : finRotate (n + 1) k = a
    · simp only [hna, ha, Bool.false_eq_true, ↓reduceIte]
    · rw [Equiv.swap_apply_of_ne_of_ne hna hnext]

/-- Only the ML edge contributes to the effect of the swap. -/
theorem wordCoefficient_swap_mul {a : Fin (n+1)}
    (ha : w a = false) (hb : w (finRotate (n+1) a) = true) (k : ℂ)
    (hk : k * (r.right (σ (finRotate (n+1) a)) * r.left (σ a) - r.collision) =
      r.right (σ a) * r.left (σ (finRotate (n+1) a)) - r.collision) :
    k * wordCoefficient r (σ * Equiv.swap a (finRotate (n+1) a)) w = wordCoefficient r σ w := by
  unfold wordCoefficient
  rw [← Finset.mul_prod_erase univ _ (mem_univ a),
    ← Finset.mul_prod_erase univ (wordEdgeFactor r σ w) (mem_univ a)]
  have hr : (∏ j ∈ univ.erase a, wordEdgeFactor r (σ * Equiv.swap a (finRotate (n+1) a)) w j) =
      ∏ j ∈ univ.erase a, wordEdgeFactor r σ w j :=
    Finset.prod_congr rfl fun j hj => wordEdgeFactor_swap_of_ne r σ w ha hb (mem_erase.mp hj).1
  rw [hr, ← mul_assoc]
  simp only [wordEdgeFactor, ha, hb, Bool.false_eq_true, ↓reduceIte,
    Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact congrArg (fun s => s * ∏ j ∈ univ.erase a, wordEdgeFactor r σ w j) hk

end

/-- Swapping momenta is equivalent to swapping their two coordinates. -/
theorem planeWave_swap {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) (a b : Fin n) :
    planeWave p (σ * Equiv.swap a b) x = planeWave p σ (fun k => x (Equiv.swap a b k)) := by
  unfold planeWave
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_self] using
    Equiv.prod_comp (Equiv.swap a b) (fun k =>
      Complex.exp (I * (p (σ k) : ℂ) * (x (Equiv.swap a b k) : ℂ)))

/-- At an ordinary ML edge both selected coordinates are the same integer. -/
theorem wordPhase_adjacent_swap {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    wordPhase (N := N) x p (σ * Equiv.swap a.castSucc a.succ) w =
      wordPhase (N := N) x p σ w := by
  change planeWave p (σ * Equiv.swap a.castSucc a.succ)
    (fun k => if w k then cyclicPredecessorPositions N x k else x k) =
    planeWave p σ (fun k => if w k then cyclicPredecessorPositions N x k else x k)
  rw [planeWave_swap]
  congr 1
  aesop

end PottsDiscontinuity.BetheAnsatz
