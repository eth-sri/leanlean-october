module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Aggregate

/-!
# Evaluation of the paired zero-root contribution

The zipper reindexing separates the nonzero-root phase derivatives from the
single cyclic seam indicator. This module evaluates that sum and combines it
with the corrected constant-word limit.
-/

public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The sum of the phase derivatives at all labels except the zero root. -/
noncomputable def t1RootDerivativeSum {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : ℂ :=
  ∑ j : {j : Fin (n + 1) // j ≠ l},
    (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)

/-- The real phase derivative is the derivative of the complexified phase. -/
theorem zeroRootPhaseDerivative_false_eq_complexDeriv {N : ℕ} {c p : ℝ}
    (hc : 2 < c) :
    (zeroRootPhaseDerivative (N := N) (anisotropy c) p False : ℂ) =
      deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t p : ℂ)) 0 := by
  have hθ :=
    (Bethe.analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 p).differentiableAt.hasDerivAt
  have hcomplex :=
    hθ.ofReal_comp.deriv
  grind [zeroRootPhaseDerivative, anisotropy, deriv, Bethe.theta]

section
variable {N n : ℕ}
/-- The subtype derivative sum is the source's erased finite sum. -/
theorem t1RootDerivativeSum_eq_erase {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    t1RootDerivativeSum (N := N) (anisotropy c) p l =
      ∑ j ∈ (univ : Finset (Fin (n + 1))).erase l,
        deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t (p j) : ℂ)) 0 := by
  rw [t1RootDerivativeSum, ← Finset.sum_subtype (univ.erase l) (fun j => by simp)
    fun j => (zeroRootPhaseDerivative (anisotropy c) (p j) False : ℂ)]
  exact sum_congr rfl fun j _ => zeroRootPhaseDerivative_false_eq_complexDeriv hc

/-- The regularized all-M word coefficient is the fixed product over nonzero
roots, times the ordinary coordinate plane wave. -/
theorem zeroRootRegularizedWordTerm_allM (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    zeroRootRegularizedWordTerm (N := N) c x p l σ (fun _ => false) =
      (c : ℂ)^2 * amplitude (anisotropy c) p σ *
        (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
        planeWave p σ x := by
  have hprod : (∏ k ∈ (univ : Finset (Fin (n + 1))).erase (σ.symm l), M c (z (p (σ k)))) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) :=
    Finset.prod_nbij' σ σ.symm (by simp [Equiv.apply_eq_iff_eq_symm_apply]) (by simp) (by simp) (by simp) (by simp)
  unfold zeroRootRegularizedWordTerm zeroRootRegularizedProduct zeroRootLetterWeight
  rw [wordPhase_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hprod]
  ring

/-- The finite paired T₁ limit after summing the allowed output slots. -/
theorem sum_t1SigmaLimitTerm_formula {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    (∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l},
      t1SigmaLimitTerm (N := N) c x p l q) =
      ((c : ℂ)^2 *
        (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)))) *
        ∑ σ : Equiv.Perm (Fin (n + 1)),
          amplitude (anisotropy c) p σ * planeWave p σ x *
            (t1RootDerivativeSum (N := N) (anisotropy c) p l +
              if σ (Fin.last n) = l then 0 else (N : ℂ)) := by
  rw [Fintype.sum_sigma, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [t1SigmaLimitTerm, ← mul_sum, zeroRootRegularizedWordTerm_allM,
    sum_t1OutputSlope_slots (Δ := anisotropy c) p l σ, t1RootDerivativeSum]
  ring

/-- Adding the constant-word limit to all paired T₁ residues gives precisely
the degenerate scalar eigenvalue times the coordinate wave. -/
theorem t0_t1_pairLimits_eq_eigenvalueZero {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    t0RegularizedSum (N := N) c x p l 0 +
      ∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i =
        eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
  rw [tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm hc x p hp hinj l hpl hBE,
    t0RegularizedSum_zero, sum_t1SigmaLimitTerm_formula, eigenvalueZero, coordinateWave,
    ← t1RootDerivativeSum_eq_erase hc, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun σ _ => ?_
  have : σ.symm l = Fin.last n ↔ σ (Fin.last n) = l := σ.symm_apply_eq.trans eq_comm
  split_ifs <;> simp_all <;> ring
end

end PottsDiscontinuity.BetheAnsatz
