module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Spectral masses and strict quadratic-form directions -/

@[expose] public section


open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

variable {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)

/-- The trace of the finite-dimensional functional calculus is the spectral sum. -/
theorem trace_cfc_eq_sum  (f : ℝ → ℝ) :
    (cfc f M).trace = ∑ i, f (hM.eigenvalues i) := by
  rw [hM.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp

/-- Positive spectral mass is a sum of nonnegative scalar positive parts. -/
theorem positiveSpectralMass_eq_sum  :
    positiveSpectralMass M = ∑ i, max 0 (hM.eigenvalues i) :=
  trace_cfc_eq_sum M hM _

/-- Every Hermitian matrix has nonnegative positive spectral mass. -/
theorem positiveSpectralMass_nonneg  (hM : M.IsHermitian) :
    0 ≤ positiveSpectralMass M := by
  rw [positiveSpectralMass_eq_sum M hM]
  positivity

/-- Zero positive spectral mass forces every quadratic form to be nonpositive. -/
theorem quadratic_nonpos_of_positiveSpectralMass_zero 
    (hM : M.IsHermitian) (hm : positiveSpectralMass M = 0) (w : PDE.Vec d) :
    dotProduct w (M.mulVec w) ≤ 0 := by
  have hs : ∀ i, hM.eigenvalues i ≤ 0 := by
    rw [positiveSpectralMass_eq_sum M hM] at hm
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_left 0
      _)).mp hm
    simp_all
  have hnonpos : M ≤ 0 := by
    conv_lhs => rw [← cfc_id (p := IsSelfAdjoint) ℝ M hM.isSelfAdjoint]
    rw [← map_zero (algebraMap ℝ (PDE.Mat d))]
    apply cfc_le_algebraMap (id : ℝ → ℝ) 0 M
      (ha := hM.isSelfAdjoint) (hf := by fun_prop)
    intro t ht
    obtain ⟨i, rfl⟩ := hM.spectrum_real_eq_range_eigenvalues ▸ ht
    grind
  have hneg : 0 ≤ -M := neg_nonneg.mpr hnonpos
  have hh := (Matrix.nonneg_iff_posSemidef.mp hneg).dotProduct_mulVec_nonneg w
  have hh' : 0 ≤ -dotProduct w (M.mulVec w) := by
    simpa only [Matrix.neg_mulVec, dotProduct_neg, star_trivial] using hh
  simp_all

/-- A positive quadratic-form direction gives strictly positive positive spectral mass. -/
theorem positiveSpectralMass_pos_of_direction 
    (hM : M.IsHermitian) (w : PDE.Vec d) (hw : 0 < dotProduct w (M.mulVec w)) :
    0 < positiveSpectralMass M := by
  have hnonneg := positiveSpectralMass_nonneg M hM
  apply lt_of_le_of_ne hnonneg
  intro hh
  exact (quadratic_nonpos_of_positiveSpectralMass_zero M hM hh.symm w).not_gt hw

/-- A negative quadratic-form direction gives strictly positive negative spectral mass. -/
theorem negativeSpectralMass_pos_of_direction 
    (hM : M.IsHermitian) (w : PDE.Vec d) (hw : dotProduct w (M.mulVec w) < 0) :
    0 < negativeSpectralMass M := by
  apply positiveSpectralMass_pos_of_direction (-M) hM.neg w
  simpa only [Matrix.neg_mulVec, dotProduct_neg] using neg_pos.mpr hw

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
