module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Ordinary
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Phase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase

/-!
# The corrected paired-term identity at the cyclic seam

The seam pair has the same ordinary scattering increment, together with the
additional `N t` phase produced by the wrapped coordinate.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- At a seam ML edge with the zero root in the L slot, the swapped perturbed
word term has the corrected phase ratio including `N t`. -/
theorem perturbedWordTerm_seam_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
    (t : ℝ) (ht : z t ≠ 1) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    perturbedWordTerm (N := N) c x p l t
        (σ * Equiv.swap (Fin.last n) 0) w =
      -Complex.exp (I * (zeroRootPhaseExponent (N := N) (anisotropy c)
        (p (σ (Fin.last n))) True t : ℂ)) *
        perturbedWordTerm (N := N) c x p l t σ w := by
  let u := Fin.last n
  let q := perturbedMomenta p l t
  have hσu : σ u ≠ l := by aesop
  have hpσu : p (σ u) ≠ 0 := by grind
  have hq0 : q (σ 0) = t := by simp [q, perturbedMomenta, hsig, hpl]
  have hqu : q (σ u) = p (σ u) := perturbedMomenta_of_ne p l (σ u) t hσu
  have hz0 : z (q (σ 0)) ≠ 1 := by simp_all
  have hzu : z (q (σ u)) ≠ 1 := by rw [hqu]; exact z_ne_one (hp (σ u)) hpσu
  let num := M c (z (q (σ 0))) * L c (z (q (σ u))) - 1
  let den := M c (z (q (σ u))) * L c (z (q (σ 0))) - 1
  have hden :=
    M_mul_L_sub_one_ne_zero hc hzu hz0
  have hcross' :
      wordCoefficient c q (σ * Equiv.swap u 0) w * den =
        wordCoefficient c q σ w * num := by
    simpa using (wordCoefficient_swap_cross c q σ w hLast (by simp_all))
  have htheta : Complex.exp (I * (Bethe.theta (anisotropy c)
      (q (σ 0)) (q (σ u)) : ℂ)) = num / den := by
    simpa using exp_I_theta_eq_M_L_ratio hc hz0 hzu
  have hzero : p (σ 0) = 0 := by simp_all
  have hamp := amplitude_seam_swap hc p hBE σ hn hzero
  have hphase := wordPhase_seam_swap (N := N) x q σ w hn hLast hZero
  have hthetaSeam :
      Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ u)) 0 : ℂ)) *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ u)) : ℂ)) * z t ^ N =
      Complex.exp (I * (zeroRootPhaseExponent (N := N) (anisotropy c)
        (p (σ u)) True t : ℂ)) := by
    rw [z, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    simp [zeroRootPhaseExponent]
    rw [Bethe.theta_swap]
    push_cast
    ring_nf
  have hzs : z (p (σ u)) ^ N ≠ 0 := pow_ne_zero N (z_ne_zero _)
  unfold perturbedWordTerm
  grind

end PottsDiscontinuity.BetheAnsatz
