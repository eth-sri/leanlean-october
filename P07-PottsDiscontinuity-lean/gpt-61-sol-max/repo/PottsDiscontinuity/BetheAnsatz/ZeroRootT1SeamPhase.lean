module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0

/-!
# The seam position-phase ratio

At the seam, swapping the two momenta changes their positions by exactly `N`.
This is the source of the extra `N t` term in the corrected T₁ phase.
-/

@[expose] public section

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
  
  have hyu : y u = x u := by simp [y, wordPositions, u, hLast]
  have hy0 : y 0 = x u -  N  := by
    simp [y, wordPositions, hZero, u]
  let f  := fun k => positionPhase (p (σ k)) (y k)
  let g  := fun k =>
    positionPhase (p (σ k)) (y (Equiv.swap u 0 k))
  
  have hphase : wordPhase (N := N) x p σ w = ∏ k, f k := rfl
  let S  := (univ.erase u).erase 0
  have hrest :  ∏ k ∈ S, g k  = ∏ k ∈ S, f k := by
    apply Finset.prod_congr rfl
    aesop
  have hsplit (q : Fin (n + 1) → ℂ) :
       ∏ k, q k  = q u * (q 0 * ∏ k ∈ S, q k) := Trans.trans (Eq.symm (mul_prod_erase univ q (mem_univ u)))
                                                   (Eq.mpr
                                                     (congrArg (fun _a => q u * _a = q u * (q 0 * S.prod q))
                                                       (Eq.symm (mul_prod_erase (univ.erase u) q (mem_erase.mpr ⟨Ne.symm (by
                                                                                                                            grind), mem_univ 0⟩))))
                                                     (Eq.refl (q u * (q 0 * ((univ.erase u).erase 0).prod q))))
  have hgPair : g u * g 0 =
      z (p (σ 0)) ^ N * (z (p (σ u)) ^ N)⁻¹ * (f u * f 0) := by
    have hgu : g u = positionPhase (p (σ u)) (x u -  N ) := by
      aesop
    have hg0 : g 0 = positionPhase (p (σ 0)) (x u) := by
      aesop
    have hfu : f u = positionPhase (p (σ u)) (x u) := by
      simp [f, hyu]
    have hf0 : f 0 = positionPhase (p (σ 0)) (x u -  N ) := by
      simp [f, hy0]
    
    
    rw [hgu, hg0, hfu, hf0,
      positionPhase_sub_nat (p (σ u)) (x u) N,
      positionPhase_sub_nat (p (σ 0)) (x u) N]
    field_simp [pow_ne_zero N (z_ne_zero _), pow_ne_zero N (z_ne_zero _)]
  calc
    wordPhase (N := N) x p (σ * Equiv.swap u 0) w = ∏ k, g k :=  by
                                                                   change planeWave p (σ * Equiv.swap u 0) y = ∏ k, g k
                                                                   rw [planeWave_swap]
                                                                   rfl 
    _ = g u * (g 0 * ∏ k ∈ S, g k) := hsplit g
    _ =  g u * g 0  * ∏ k ∈ S, g k := by ring
    _ = z (p (σ 0)) ^ N * (z (p (σ u)) ^ N)⁻¹ *
          (f u * (f 0 * ∏ k ∈ S, f k)) := by rw [hgPair, hrest]; ring
    _ = z (p (σ 0)) ^ N * (z (p (σ u)) ^ N)⁻¹ * wordPhase (N := N) x p σ w := by
      rw [← hsplit f, hphase]

end PottsDiscontinuity.BetheAnsatz
