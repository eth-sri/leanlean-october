module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Spectral masses and strict quadratic-form directions -/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

variable {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) (hm : positiveSpectralMass M = 0)
    (w : PDE.Vec d)

/-- The trace of the finite-dimensional functional calculus is the spectral sum. -/
theorem trace_cfc_eq_sum (f : ℝ → ℝ) :
    (cfc f M).trace = ∑ i, f (hM.eigenvalues i) := by
  rw [hM.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp

/-- Positive spectral mass is a sum of nonnegative scalar positive parts. -/
theorem positiveSpectralMass_eq_sum :
    positiveSpectralMass M = ∑ i, max 0 (hM.eigenvalues i) :=
  trace_cfc_eq_sum M hM _

include hM in
/-- Every Hermitian matrix has nonnegative positive spectral mass. -/
theorem positiveSpectralMass_nonneg :
    0 ≤ positiveSpectralMass M := by
  rw [positiveSpectralMass_eq_sum M hM]
  positivity

include hM hm in
/-- Zero positive spectral mass forces every quadratic form to be nonpositive. -/
theorem quadratic_nonpos_of_positiveSpectralMass_zero :
    dotProduct w (M.mulVec w) ≤ 0 := by
  have hs : ∀ i, hM.eigenvalues i ≤ 0 := by
    rw [positiveSpectralMass_eq_sum M hM] at hm
    intro i
    have hh := ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_left 0 (hM.eigenvalues i))).mp hm) i (Finset.mem_univ i)
    grind
  have hnonpos : M ≤ 0 := by
    conv_lhs => rw [← cfc_id (p := IsSelfAdjoint) ℝ M hM.isSelfAdjoint]
    rw [← map_zero (algebraMap ℝ (PDE.Mat d))]
    apply cfc_le_algebraMap id 0 M
      (ha := hM.isSelfAdjoint) (hf := by fun_prop)
    intro t ht
    obtain ⟨i, rfl⟩ := hM.spectrum_real_eq_range_eigenvalues ▸ ht
    apply hs
  have hh := (Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr hnonpos)).dotProduct_mulVec_nonneg w
  have hh' : 0 ≤ -dotProduct w (M.mulVec w) := by
    simpa [Matrix.neg_mulVec] using hh
  exact neg_nonneg.mp hh'

include hM in
/-- A positive quadratic-form direction gives strictly positive positive spectral mass. -/
theorem positiveSpectralMass_pos_of_direction (hw : 0 < dotProduct w (M.mulVec w)) :
    0 < positiveSpectralMass M := by
  apply lt_of_le_of_ne (positiveSpectralMass_nonneg M hM)
  intro hh
  exact (quadratic_nonpos_of_positiveSpectralMass_zero M hM hh.symm w).not_gt hw

include hM in
/-- A negative quadratic-form direction gives strictly positive negative spectral mass. -/
theorem negativeSpectralMass_pos_of_direction (hw : dotProduct w (M.mulVec w) < 0) :
    0 < negativeSpectralMass M := by
  apply positiveSpectralMass_pos_of_direction (-M) hM.neg w
  simpa [Matrix.neg_mulVec] using neg_pos.mpr hw

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
