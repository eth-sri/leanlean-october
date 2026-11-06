module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.Perturbation
public import PottsDiscontinuity.BetheAnsatz.WordSwap

/-!
# Ordinary-edge pairing in the zero-root perturbation

With the amplitudes held at the original Bethe roots, an ordinary ML edge
still has a pair relation. The moved root contributes its phase explicitly;
this is the corrected Claim 1 ratio from the source audit.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- One amplitude-weighted word term with only the word momentum perturbed. -/
noncomputable def perturbedWordTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)  :=
  amplitude (anisotropy c) p σ *
    wordCoefficient c (perturbedMomenta p l t) σ w *
      wordPhase (N := N) x (perturbedMomenta p l t) σ w

/-- At an ordinary ML edge whose L slot carries the moved root, swapping the
two slots multiplies the perturbed word term by the corrected scattering phase. -/
theorem perturbedWordTerm_adjacent_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (t : ℝ) (ht : z t ≠ 1)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    perturbedWordTerm (N := N) c x p l t (σ * Equiv.swap a.castSucc a.succ) w =
      -Complex.exp (I * (Bethe.theta (anisotropy c) t (p (σ a.castSucc)) -
        Bethe.theta (anisotropy c) 0 (p (σ a.castSucc)) : ℂ)) *
        perturbedWordTerm (N := N) c x p l t σ w := by
  let q := perturbedMomenta p l t
  
  have hσa : σ a.castSucc ≠ l := by
    aesop
  
  have hqa : q (σ a.castSucc) = p (σ a.castSucc) :=
    by
      solve_by_elim [_root_.PottsDiscontinuity.BetheAnsatz.perturbedMomenta_of_ne]
  have hqb : q (σ a.succ) = t := by
    aesop
  have hqa_ne : z (q (σ a.castSucc)) ≠ 1 := by
    rw [hqa]
    exact z_ne_one (hp (σ a.castSucc)) ( fun j hj => by
                                           grind  _ hσa)
  
  have hrot : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hcross := wordCoefficient_swap_cross c q σ w ha (hrot.symm ▸ hb)
  
  
  let den := M c (z (q (σ a.castSucc))) * L c (z (q (σ a.succ))) - 1
  have hden : den ≠ 0 := M_mul_L_sub_one_ne_zero hc hqa_ne (by rw [hqb]; exact ht)
  
  have htheta : Complex.exp (I *  Bethe.theta (anisotropy c)
        (q (σ a.succ)) (q (σ a.castSucc)) ) = (M c (z (q (σ a.succ))) * L c (z (q (σ a.castSucc))) - 1) / den := exp_I_theta_eq_M_L_ratio hc (by rw [hqb]; exact ht) hqa_ne
  
  
  
  
  
  
  have hfactor : Complex.exp (I *  Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 ) *
      Complex.exp (I *  Bethe.theta (anisotropy c) t (p (σ a.castSucc)) ) =
      Complex.exp (I * (Bethe.theta (anisotropy c) t (p (σ a.castSucc)) -
        Bethe.theta (anisotropy c) 0 (p (σ a.castSucc)) )) := by
    rw [← Complex.exp_add]
    
    rw [Bethe.theta_swap, Complex.ofReal_neg]
    ring
  unfold perturbedWordTerm
  rw [(by
         rw [amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ (by simp), hsig, hpl] : amplitude (anisotropy c) p (σ * Equiv.swap a.castSucc a.succ) =
      -Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 )) * amplitude (anisotropy c) p σ),  wordPhase_adjacent_swap x q σ w a ha hb ]
  calc
     -Complex.exp (I *  Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 ) * amplitude (anisotropy c) p σ  *
        wordCoefficient c (perturbedMomenta p l t)
          (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w =
       -Complex.exp (I *  Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 ) * amplitude (anisotropy c) p σ  *
        (wordCoefficient c (perturbedMomenta p l t)
          (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w) := by ring
    _ =  -Complex.exp (I *  Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 ) * amplitude (anisotropy c) p σ  *
        (Complex.exp (I *  Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) ) *
          (wordCoefficient c (perturbedMomenta p l t) σ w *
            wordPhase (N := N) x q σ w)) := by rw [ (by
                                                       grind :
      wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w =
        Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) )) *
          (wordCoefficient c q σ w * wordPhase (N := N) x q σ w)) ]
    _ = -(Complex.exp (I *  Bethe.theta (anisotropy c)
          (p (σ a.castSucc)) 0 ) *
        Complex.exp (I *  Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) )) *
        (amplitude (anisotropy c) p σ *
          wordCoefficient c (perturbedMomenta p l t) σ w *
          wordPhase (N := N) x q σ w) := by ring
    _ = -Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) - Bethe.theta (anisotropy c) 0
            (p (σ a.castSucc)) )) *
        (amplitude (anisotropy c) p σ *
          wordCoefficient c (perturbedMomenta p l t) σ w *
          wordPhase (N := N) x q σ w) := by
      rw [hfactor]

end PottsDiscontinuity.BetheAnsatz
