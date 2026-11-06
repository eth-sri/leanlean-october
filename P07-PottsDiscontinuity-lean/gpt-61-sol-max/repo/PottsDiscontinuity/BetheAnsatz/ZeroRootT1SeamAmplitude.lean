module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.Cyclic

/-!
# The seam amplitude transposition

Conjugating the seam swap by the cyclic rotation turns it into the ordinary
swap of slots 0 and 1. The cyclic Bethe relation then gives its boundary factor.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The amplitude ratio for swapping the last and first slots, with the first
slot carrying a zero root. -/
theorem amplitude_seam_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (hn : 0 < n)
    (hzero : p (σ 0) = 0) :
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
      - z (p (σ (Fin.last n))) ^ N  *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) 0 : ℂ)) * amplitude (anisotropy c) p σ := by
  let τ := finRotate (n + 1)
  let ρ := σ * τ.symm
  have hlast : τ (Fin.last n) = 0 := finRotate_last
  let j : Fin n := ⟨0, hn⟩
  
  have hjsucc : j.succ =  1  := by
    apply Fin.ext
    simp [j, Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
  
  have hinvzero  :=
    (Equiv.symm_apply_eq _).mpr hlast.symm
  
  have hEq : (τ.trans (Equiv.swap 0 1)).trans τ.symm =
      Equiv.swap (Fin.last n) 0 := by
    aesop
  have hconj : τ.symm * Equiv.swap  0  1 * τ =
      Equiv.swap (Fin.last n) 0 := by
    assumption
  
  have hρzero : ρ 0 = σ (Fin.last n) := by
    simp [ρ, hinvzero]
  have hρone : ρ 1 = σ 0 := by
    simp [ρ, Equiv.Perm.mul_apply,  (Equiv.symm_apply_eq _).mpr (by
                                                                   aesop : τ 0 = 1).symm ]
  
  have hrot  :=
    amplitude_rotate (anisotropy_lt_neg_one hc) p hBE ρ
  have hτinv : τ.symm * τ = 1 := by
    ext k
    simp
  
  
  
  
  have hAdj := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p ρ
    (a := j.castSucc) (b := j.succ) (by simp)
  rw [(by  simp [j] : j.castSucc = (0 )), hjsucc, hρzero, hρone, hzero] at hAdj
  calc
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
        amplitude (anisotropy c) p
          ( ρ * Equiv.swap  0  1  * τ) := by rw [(by
                                                     grind : σ * Equiv.swap (Fin.last n) 0 =  ρ * Equiv.swap 0 1  * τ)]
    _ = amplitude (anisotropy c) p (ρ * Equiv.swap 0 1) :=  by
                                                              rw [amplitude_rotate (anisotropy_lt_neg_one hc) p hBE]
                                                              rw [(by
                                                                     simp [hρone] : (ρ * Equiv.swap (0 : Fin (n + 1)) 1) 0 = σ 0), hzero]
                                                              simp  
    _ = -Complex.exp (I *  Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) 0 ) * amplitude (anisotropy c) p ρ := hAdj
    _ = - z (p (σ (Fin.last n))) ^ N  *
          Complex.exp (I *  Bethe.theta (anisotropy c)
            (p (σ (Fin.last n))) 0 ) * amplitude (anisotropy c) p σ := by
      rw [(by
             have hz : z (p (σ (Fin.last n))) ^ N ≠ 0 :=
               pow_ne_zero N (z_ne_zero _)
             grind : amplitude (anisotropy c) p ρ =
      z (p (σ (Fin.last n))) ^ N * amplitude (anisotropy c) p σ)]
      ring

end PottsDiscontinuity.BetheAnsatz
