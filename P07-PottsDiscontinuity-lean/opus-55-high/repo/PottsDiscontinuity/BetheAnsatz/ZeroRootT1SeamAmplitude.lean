module

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.Cyclic

/-!
# The seam amplitude transposition

Conjugating the seam swap by the cyclic rotation turns it into the ordinary
swap of slots 0 and 1. The cyclic Bethe relation then gives its boundary factor.
-/

public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The boundary amplitude ratio follows from the cyclic Bethe relation and
the ordinary adjacent amplitude relation. The zero-root specialization is
`amplitude_seam_swap`. -/
theorem amplitude_seam_swap_general {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (hn : 0 < n) :
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
      -(z (p (σ (Fin.last n))) ^ N) *
        (z (p (σ 0)) ^ N)⁻¹ *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
        amplitude (anisotropy c) p σ := by
  let τ := finRotate (n + 1)
  let ρ := σ * τ.symm
  let j : Fin n := ⟨0, hn⟩
  have hjcast : j.castSucc = (0 : Fin (n + 1)) := by rfl
  have hjsucc : j.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    simp [j, Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
  have hinvzero : τ.symm 0 = Fin.last n :=
    by rfl
  have hinvone : τ.symm 1 = 0 :=
    by aesop
  have hEq : (τ.trans (Equiv.swap (0 : Fin (n + 1)) 1)).trans τ.symm =
      Equiv.swap (Fin.last n) 0 := by
    aesop
  have hconj : τ.symm * Equiv.swap (0 : Fin (n + 1)) 1 * τ =
      Equiv.swap (Fin.last n) 0 := by
    tauto
  have hρzero : ρ 0 = σ (Fin.last n) := by
    rfl
  have hρone : ρ 1 = σ 0 := by
    simp [ρ, Equiv.Perm.mul_apply, hinvone]
  have hρswapzero : (ρ * Equiv.swap (0 : Fin (n + 1)) 1) 0 = ρ 1 := by
    rfl
  have hτinv : τ.symm * τ = 1 := by ext k; simp
  have hρamp : amplitude (anisotropy c) p ρ =
      z (p (σ (Fin.last n))) ^ N * amplitude (anisotropy c) p σ := by
    have hz : z (p (σ (Fin.last n))) ^ N ≠ 0 :=
      pow_ne_zero N (z_ne_zero _)
    have hrot := amplitude_rotate (anisotropy_lt_neg_one hc) p hBE ρ
    grind
  have hρswapAmp := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p ρ
      (a := j.castSucc) (b := j.succ) (by simp)
  have hrotSwap := amplitude_rotate (anisotropy_lt_neg_one hc) p hBE
    (ρ * Equiv.swap (0 : Fin (n + 1)) 1)
  grind
/-- The amplitude ratio for swapping the last and first slots, with the first
slot carrying a zero root. -/
theorem amplitude_seam_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (hn : 0 < n)
    (hzero : p (σ 0) = 0) :
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
      -(z (p (σ (Fin.last n))) ^ N) *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) 0 : ℂ)) * amplitude (anisotropy c) p σ := by
  simp [amplitude_seam_swap_general hc p hBE σ hn, hzero, z]

end PottsDiscontinuity.BetheAnsatz
