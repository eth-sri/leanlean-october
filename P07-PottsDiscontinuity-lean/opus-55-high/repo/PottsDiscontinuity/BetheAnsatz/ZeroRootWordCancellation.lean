module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude

/-!
# Cancellation away from the perturbed zero root

The amplitudes remain at the original Bethe roots while word coefficients and
phases use the perturbed tuple. A cyclic ML edge still cancels whenever neither
endpoint carries the root label being perturbed.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {N n : ℕ}
/-- A word term with amplitudes fixed at `p` and local weights evaluated at `q`. -/
noncomputable def fixedAmplitudeWordTerm (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * wordCoefficient c q σ w *
    wordPhase (N := N) x q σ w

end

section
variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (p q : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℤ)
include c hc x
/-- At an ordinary ML edge away from the perturbed label, the two
fixed-amplitude terms cancel. -/
theorem fixedAmplitudeWordTerm_adjacent_swap (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true)
    (hqa : q (σ a.castSucc) = p (σ a.castSucc))
    (hqb : q (σ a.succ) = p (σ a.succ))
    (hza : z (p (σ a.castSucc)) ≠ 1) (hzb : z (p (σ a.succ)) ≠ 1) :
    fixedAmplitudeWordTerm (N := N) c x p q
        (σ * Equiv.swap a.castSucc a.succ) w =
      -fixedAmplitudeWordTerm (N := N) c x p q σ w := by
  have hr := finRotate_of_lt a.isLt
  have hcross := wordCoefficient_swap_cross c q σ w ha (by
    simp_all)
  have he := M_mul_L_sub_one_ne_zero hc hzb hza
  have hphase := wordPhase_adjacent_swap (N := N) x q σ w a ha hb
  have hab : (a.castSucc).val + 1 = (a.succ).val := rfl
  have hamp := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ hab
  have hfactor :
      Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) (p (σ a.succ)) : ℂ)) *
        wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w =
      wordCoefficient c q σ w := by
    rw [exp_I_theta_eq_M_L_ratio hc hza hzb]
    grind
  grind [fixedAmplitudeWordTerm, Complex.exp, I, Bethe.theta, anisotropy, amplitude, wordCoefficient, Equiv.swap]

/-- At the cyclic seam, the Bethe and position phases cancel whenever the
perturbed root is not at either endpoint. -/
theorem fixedAmplitudeWordTerm_seam_swap (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hLast : w (Fin.last n) = false) (hZero : w 0 = true)
    (hqLast : q (σ (Fin.last n)) = p (σ (Fin.last n)))
    (hqZero : q (σ 0) = p (σ 0))
    (hzLast : z (p (σ (Fin.last n))) ≠ 1) (hzZero : z (p (σ 0)) ≠ 1) :
    fixedAmplitudeWordTerm (N := N) c x p q
        (σ * Equiv.swap (Fin.last n) 0) w =
      -fixedAmplitudeWordTerm (N := N) c x p q σ w := by
  have hcross := wordCoefficient_swap_cross c q σ w
      hLast (by simp_all)
  simp_all
  have he := M_mul_L_sub_one_ne_zero hc hzZero hzLast
  have hphase := wordPhase_seam_swap (N := N) x q σ w hn hLast hZero
  have hamp := amplitude_seam_swap_general hc p hBE σ hn
  have hfactor :
      Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
        wordCoefficient c q (σ * Equiv.swap (Fin.last n) 0) w =
      wordCoefficient c q σ w := by
    rw [exp_I_theta_eq_M_L_ratio hc hzLast hzZero]
    grind
  unfold fixedAmplitudeWordTerm
  have hz0 : z (p (σ 0)) ^ N ≠ 0 := pow_ne_zero N (z_ne_zero _)
  have hzu : z (p (σ (Fin.last n))) ^ N ≠ 0 :=
    pow_ne_zero N (z_ne_zero _)
  grind
end

end PottsDiscontinuity.BetheAnsatz
