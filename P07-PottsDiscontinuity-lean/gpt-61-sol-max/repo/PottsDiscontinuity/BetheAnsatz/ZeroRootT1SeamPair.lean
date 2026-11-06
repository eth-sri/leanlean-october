module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Ordinary
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Phase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase

/-!
# The corrected paired-term identity at the cyclic seam

The seam pair has the same ordinary scattering increment, together with the
additional `N t` phase produced by the wrapped coordinate.
-/

@[expose] public section

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
  have hu0 : u ≠  0  := by
    grind
  have hσu : σ u ≠ l := by
    aesop
  
  have hq0 : q (σ 0) = t := by aesop
  have hqu : q (σ u) = p (σ u) := by
                                    solve_by_elim [_root_.PottsDiscontinuity.BetheAnsatz.perturbedMomenta_of_ne]
  
  have hzu : z (q (σ u)) ≠ 1 := by rw [hqu]; exact z_ne_one (hp (σ u)) (by
                                                                          grind)
  let num := M c (z (q (σ 0))) * L c (z (q (σ u))) - 1
  let den := M c (z (q (σ u))) * L c (z (q (σ 0))) - 1
  have hden : den ≠ 0 := M_mul_L_sub_one_ne_zero hc hzu (by rw [hq0]; exact ht)
  
  have hcross' :
      wordCoefficient c q (σ * Equiv.swap u 0) w * den =
        wordCoefficient c q σ w * num := by
    simpa  using  wordCoefficient_swap_cross c q σ w hLast (by simpa using hZero) 
  have htheta : Complex.exp (I *  Bethe.theta (anisotropy c)
      (q (σ 0)) (q (σ u)) ) = num / den := exp_I_theta_eq_M_L_ratio hc (by rw [hq0]; exact ht) hzu
  
  have hcoeff : wordCoefficient c q (σ * Equiv.swap u 0) w =
      Complex.exp (I *  Bethe.theta (anisotropy c)
        (q (σ 0)) (q (σ u)) ) * wordCoefficient c q σ w := by
    grind
  rw [hq0, hqu] at hcoeff
  
  
  have hphase := wordPhase_seam_swap (N := N) x q σ w hn hLast hZero
  rw [hq0, hqu] at hphase
  have hzpow : z t ^ N = Complex.exp (I *  N  *  t ) := by
    rw [z, ← Complex.exp_nat_mul]
    
    ring
  have hthetaSeam :
      Complex.exp (I *  Bethe.theta (anisotropy c)
          (p (σ u)) 0 ) *
        Complex.exp (I *  Bethe.theta (anisotropy c)
          t (p (σ u)) ) * z t ^ N =
      Complex.exp (I *  zeroRootPhaseExponent (N := N) (anisotropy c)
        (p (σ u)) True t ) := by
    rw [hzpow, ← Complex.exp_add, ← Complex.exp_add]
    
    simp [zeroRootPhaseExponent]
    rw [Bethe.theta_swap]
    push_cast
    ring
  have hscalar :
      - z (p (σ u)) ^ N  *
        Complex.exp (I *  Bethe.theta (anisotropy c) (p (σ u)) 0 ) *
        Complex.exp (I *  Bethe.theta (anisotropy c) t (p (σ u)) ) *
        z t ^ N * (z (p (σ u)) ^ N)⁻¹ =
      -Complex.exp (I *  zeroRootPhaseExponent (N := N) (anisotropy c)
        (p (σ u)) True t ) := by
    have hzs : z (p (σ u)) ^ N ≠ 0 := pow_ne_zero N (z_ne_zero _)
    grind
  
  calc
    amplitude (anisotropy c) p (σ * Equiv.swap u 0) *
        wordCoefficient c q (σ * Equiv.swap u 0) w *
        wordPhase (N := N) x q (σ * Equiv.swap u 0) w =
       - z (p (σ u)) ^ N  *
        Complex.exp (I *  Bethe.theta (anisotropy c) (p (σ u)) 0 ) *
        amplitude (anisotropy c) p σ  *
        (Complex.exp (I *  Bethe.theta (anisotropy c) t (p (σ u)) ) *
          wordCoefficient c q σ w) *
        (z t ^ N * (z (p (σ u)) ^ N)⁻¹ *
          wordPhase (N := N) x q σ w) := by
        rw [ amplitude_seam_swap hc p hBE σ hn (by rw [hsig, hpl]) , hcoeff, hphase]
    _ = -Complex.exp (I *  zeroRootPhaseExponent (N := N) (anisotropy c)
          (p (σ u)) True t ) *
        (amplitude (anisotropy c) p σ * wordCoefficient c q σ w *
          wordPhase (N := N) x q σ w) := by
        grind

end PottsDiscontinuity.BetheAnsatz
