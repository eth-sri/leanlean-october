/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineLineLeading
public import CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates

/-! A direction where the highest homogeneous component is nonzero gives full
outer degree after the explicit affine coordinate change. Its leading
coefficient is the scalar obtained by evaluating that component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma optionEquivLeft_top_coefficient_constant {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (d : ℕ) (hd : f.totalDegree ≤ d) :
    (optionEquivLeft K σ f).coeff d = C (eval (0 : σ → K) ((optionEquivLeft K σ f).coeff d)) := by
  by_cases h : d ≤ f.totalDegree
  · have ht := totalDegree_coeff_optionEquivLeft_add_le K σ f d h
    simpa [eval_zero, constantCoeff_eq] using totalDegree_eq_zero_iff_eq_C.mp (by omega)
  · have hn : (optionEquivLeft K σ f).natDegree < d := by
      rw [natDegree_optionEquivLeft]
      exact (degreeOf_le_totalDegree f none).trans_lt (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero, map_zero]

section

variable {K σ : Type*} [Field K]
  (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
include K σ a b hb f

private lemma hypersurfaceAffineCoordinates_axis :
    Polynomial.map (eval (0 : σ → K))
      (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)) =
      affineLinePolynomial a b f := by
  let φ := (Polynomial.mapRingHom (eval (0 : σ → K))).comp
    ((optionEquivLeft K σ).toRingHom.comp (hypersurfaceAffineCoordinates a b hb).toRingHom)
  refine RingHom.congr_fun (f := φ) ?_ f
  apply MvPolynomial.ringHom_ext
  · simp [φ, affineLinePolynomial]
  · intro i
    cases i <;> simp [φ, hypersurfaceAffineCoordinates_X, affineLinePolynomial]

/-- The top outer coefficient is a constant polynomial, and its scalar is
exactly the leading homogeneous form evaluated on the chosen direction. -/
theorem hypersurfaceAffineCoordinates_top_coefficient :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree =
      C (eval b (homogeneousComponent f.totalDegree f)) := by
  rw [optionEquivLeft_top_coefficient_constant _ _
    (hypersurfaceAffineCoordinates_totalDegree_le a b hb f)]
  congr 1
  rw [← Polynomial.coeff_map, hypersurfaceAffineCoordinates_axis,
    affineLinePolynomial_top_coefficient a b f _ le_rfl]

/-- Nonvanishing in the direction forces the outer degree to be the original
total degree, even after moving an arbitrary base point to the origin. -/
theorem hypersurfaceAffineCoordinates_full_outer_degree
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).natDegree = f.totalDegree := by
  have hc :
      (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree ≠ 0 := by
    rw [hypersurfaceAffineCoordinates_top_coefficient]
    exact (map_ne_zero_iff _ (C_injective σ K)).mpr hdir
  apply le_antisymm
  · rw [natDegree_optionEquivLeft]
    exact (degreeOf_le_totalDegree _ none).trans
      (hypersurfaceAffineCoordinates_totalDegree_le a b hb f)
  · exact Polynomial.le_natDegree_of_ne_zero hc

end

end
end CCDN
