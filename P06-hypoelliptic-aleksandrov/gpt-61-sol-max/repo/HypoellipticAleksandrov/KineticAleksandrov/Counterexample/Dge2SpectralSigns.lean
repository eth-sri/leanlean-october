module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Spectral masses and strict quadratic-form directions -/

 public section



open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The trace of the finite-dimensional functional calculus is the spectral sum. -/
theorem trace_cfc_eq_sum {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (cfc f M).trace = ∑ i, f (hM.eigenvalues i) := by
  rw [hM.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal, Function.comp_def]

variable {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)

/-- Positive spectral mass is a sum of nonnegative scalar positive parts. -/
theorem positiveSpectralMass_eq_sum  :
    positiveSpectralMass M = ∑ i, max 0 (hM.eigenvalues i) :=
  trace_cfc_eq_sum M hM _

include hM in
/-- Every Hermitian matrix has nonnegative positive spectral mass. -/
theorem positiveSpectralMass_nonneg  :
    0 ≤ positiveSpectralMass M := by
  rw [positiveSpectralMass_eq_sum M hM]
  exact Finset.sum_nonneg (fun _ _ => le_max_left _ _)

include hM in
/-- Zero positive spectral mass forces every quadratic form to be nonpositive. -/
theorem quadratic_nonpos_of_positiveSpectralMass_zero  (hm : positiveSpectralMass M = 0) (w : PDE.Vec d) :
    dotProduct w (M.mulVec w) ≤ 0 := by



  have hh := (Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr (show M ≤ 0 by
      conv_lhs => rw [← cfc_id  ℝ M hM.isSelfAdjoint]
      rw [← map_zero (algebraMap ℝ (PDE.Mat d))]
      apply cfc_le_algebraMap (id : ℝ → ℝ) 0 M
        (ha := hM.isSelfAdjoint) (hf := by fun_prop)
      intro t ht
      obtain ⟨i, rfl⟩ := hM.spectrum_real_eq_range_eigenvalues ▸ ht
      exact (show ∀ i, hM.eigenvalues i ≤ 0 by
          rw [positiveSpectralMass_eq_sum M hM] at hm
          have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_left 0
            (hM.eigenvalues i))).mp hm
          intro i
          have hh := hz i (Finset.mem_univ i)
          exact (le_max_right 0 _).trans (le_of_eq hh)) i))).dotProduct_mulVec_nonneg w

  exact neg_nonneg.mp (by
      simpa only [Matrix.neg_mulVec, dotProduct_neg, star_trivial] using hh)

variable (w : PDE.Vec d)

include hM
/-- A positive quadratic-form direction gives strictly positive positive spectral mass. -/
theorem positiveSpectralMass_pos_of_direction   (hw : 0 < dotProduct w (M.mulVec w)) :
    0 < positiveSpectralMass M := by

  apply lt_of_le_of_ne (positiveSpectralMass_nonneg M hM)
  intro hh
  exact (quadratic_nonpos_of_positiveSpectralMass_zero M hM hh.symm w).not_gt hw

/-- A negative quadratic-form direction gives strictly positive negative spectral mass. -/
theorem negativeSpectralMass_pos_of_direction   (hw : dotProduct w (M.mulVec w) < 0) :
    0 < negativeSpectralMass M := by
  apply positiveSpectralMass_pos_of_direction (-M) hM.neg w
  simpa only [Matrix.neg_mulVec, dotProduct_neg] using neg_pos.mpr hw

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
