module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0

/-!
# The seam position-phase ratio

At the seam, swapping the two momenta changes their positions by exactly `N`.
This is the source of the extra `N t` term in the corrected T₁ phase.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Swapping momenta across the cyclic seam contributes the factor
`z(p₀)^N / z(p_last)^N` to the selected-position phase. -/
theorem wordPhase_seam_swap {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    wordPhase (N := N) x p (σ * Equiv.swap (Fin.last n) 0) w =
      z (p (σ 0)) ^ N * (z (p (σ (Fin.last n))) ^ N)⁻¹ *
        wordPhase (N := N) x p σ w := by
  let u := Fin.last n
  let y := wordPositions N x w
  have hu0 : u ≠ (0 : Fin (n + 1)) := by
    grind
  have hyu : y u = x u := by grind [wordPositions]
  have hy0 : y 0 = x u - (N : ℤ) := by
    simp [y, wordPositions, hZero, cyclicPredecessorPositions_zero, u]
  let f : Fin (n + 1) → ℂ := fun k => positionPhase (p (σ k)) (y k)
  let g : Fin (n + 1) → ℂ := fun k =>
    positionPhase (p (σ k)) (y (Equiv.swap u 0 k))
  have hphaseSwap : wordPhase (N := N) x p (σ * Equiv.swap u 0) w =
      ∏ k, g k := by
    change planeWave p (σ * Equiv.swap u 0) y = ∏ k, g k
    rw [planeWave_swap]
    rfl
  have hphase : wordPhase (N := N) x p σ w = ∏ k, f k := by
    rfl
  let S : Finset (Fin (n + 1)) := (univ.erase u).erase 0
  have hrest : (∏ k ∈ S, g k) = ∏ k ∈ S, f k := by
    apply Finset.prod_congr rfl
    aesop
  have hsplit (q : Fin (n + 1) → ℂ) :
      (∏ k, q k) = q u * (q 0 * ∏ k ∈ S, q k) := by
    rw [← mul_prod_erase _ q (mem_univ u), ← mul_prod_erase _ q (mem_erase.mpr ⟨hu0.symm, mem_univ 0⟩)]
  have hgPair : g u * g 0 =
      z (p (σ 0)) ^ N * (z (p (σ u)) ^ N)⁻¹ * (f u * f 0) := by
    have hgu : g u = positionPhase (p (σ u)) (x u - (N : ℤ)) := by
      simp [g, y, hy0, u]
    have hg0 : g 0 = positionPhase (p (σ 0)) (x u) := by
      simp [g, y, u, hyu]
    have hfu : f u = positionPhase (p (σ u)) (x u) := by
      grind
    have hf0 : f 0 = positionPhase (p (σ 0)) (x u - (N : ℤ)) := by
      grind
    have hzu : z (p (σ u)) ≠ 0 := z_ne_zero _
    have hz0 : z (p (σ 0)) ≠ 0 := z_ne_zero _
    rw [hgu, hg0, hfu, hf0,
      positionPhase_sub_nat (p (σ u)) (x u) N,
      positionPhase_sub_nat (p (σ 0)) (x u) N]
    field_simp [pow_ne_zero N hzu, pow_ne_zero N hz0]
  rw [hphaseSwap, hphase, hsplit g, hsplit f, hrest]
  linear_combination (∏ k ∈ S, f k) * hgPair

end PottsDiscontinuity.BetheAnsatz
