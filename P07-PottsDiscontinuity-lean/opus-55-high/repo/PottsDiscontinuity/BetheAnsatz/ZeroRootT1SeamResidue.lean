module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Residue
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPair

/-!
# The seam residue and paired limit

At a seam ML edge the unique pole is the cyclic edge from the last slot to
slot zero. Its residue combines with the corrected phase slope containing `N`.
-/

public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {N n : ℕ} {c : ℝ}
include c
/-- A T₁ pair with phase relation `hpair` has a finite limit with the corrected phase slope. -/
theorem tendsto_T1_pair (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (e : Fin (n + 1)) (seam : Prop) [Decidable seam]
    (hsig : σ (finRotate (n + 1) e) = l) (ha : w e = false) (hb : w (finRotate (n + 1) e) = true)
    (hpair : ∀ t, z t ≠ 1 → perturbedWordTerm (N := N) c x p l t
        (σ * Equiv.swap e (finRotate (n + 1) e)) w =
      -Complex.exp (I * (zeroRootPhaseExponent (N := N) (anisotropy c) (p (σ e)) seam t : ℂ)) *
        perturbedWordTerm (N := N) c x p l t σ w) :
    Tendsto (fun t : ℝ => perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t (σ * Equiv.swap e (finRotate (n + 1) e)) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (((c : ℂ)^2 * amplitude (anisotropy c) p σ * M c (z (p (σ e))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w e *
          wordPhase (N := N) x p σ w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c) (p (σ e)) seam : ℂ))) := by
  refine Tendsto.congr' ?_ (tendsto_pole_mul_one_sub_of_hasDerivAt
    (hasDerivAt_zeroRootPhaseExp (p := p (σ e)) hc seam)
    (by simp [zeroRootPhaseExponent]; split_ifs <;> simp) (tendsto_t_mul_perturbedWordTerm x p l hpl σ w e hsig ha hb))
  filter_upwards [eventually_z_ne_one_zero] with t ht
  rw [hpair t ht]
  ring
end

end PottsDiscontinuity.BetheAnsatz
