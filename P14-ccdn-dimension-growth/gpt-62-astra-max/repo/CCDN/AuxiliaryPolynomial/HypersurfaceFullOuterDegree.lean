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

variable {K σ : Type*} [Field K] (a b : Option σ → K) (hb : b none ≠ 0)
    (f : MvPolynomial (Option σ) K)

private lemma optionEquivLeft_top_coefficient_constant (d : ℕ) (hd : f.totalDegree ≤ d) :
    (optionEquivLeft K σ f).coeff d = C (eval (0 : σ → K) ((optionEquivLeft K σ f).coeff d)) := by
  by_cases h : d ≤ f.totalDegree
  · have ht := totalDegree_coeff_optionEquivLeft_add_le K σ f d h
    have hz : ((optionEquivLeft K σ f).coeff d).totalDegree = 0 := by omega
    simpa only [eval_zero, constantCoeff_eq] using totalDegree_eq_zero_iff_eq_C.mp hz
  · have hn : (optionEquivLeft K σ f).natDegree < d := by
      rw [natDegree_optionEquivLeft]
      exact (degreeOf_le_totalDegree f none).trans_lt (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero, map_zero]

private lemma hypersurfaceAffineCoordinates_axis :
    Polynomial.map (eval (0 : σ → K))
      (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)) =
      affineLinePolynomial a b f := by
  let φ := (Polynomial.mapRingHom (eval 0)).comp
    ((optionEquivLeft K σ).toRingHom.comp (hypersurfaceAffineCoordinates a b hb).toRingHom)
  have he : φ = affineLinePolynomial a b := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Polynomial.map (eval 0)
        (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb (C r))) = _
      rw [show hypersurfaceAffineCoordinates a b hb (C r) = C r from
        (hypersurfaceAffineCoordinates a b hb).commutes r]
      simp [affineLinePolynomial]
    · intro i
      change Polynomial.map (eval 0)
        (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb (X i))) = _
      rw [hypersurfaceAffineCoordinates_X]
      cases i <;> simp [affineLinePolynomial]
  exact RingHom.congr_fun he f

/-- The top outer coefficient is a constant polynomial, and its scalar is
exactly the leading homogeneous form evaluated on the chosen direction. -/
theorem hypersurfaceAffineCoordinates_top_coefficient :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree =
      C (eval b (homogeneousComponent f.totalDegree f)) := by
  rw [optionEquivLeft_top_coefficient_constant _ _
    (hypersurfaceAffineCoordinates_totalDegree_le a b hb f)]
  have h := congrArg (fun q : Polynomial K => q.coeff f.totalDegree)
    (hypersurfaceAffineCoordinates_axis a b hb f)
  grind [Polynomial.coeff_map, affineLinePolynomial_top_coefficient, le_rfl]

/-- Nonvanishing in the direction forces the outer degree to be the original
total degree, even after moving an arbitrary base point to the origin. -/
theorem hypersurfaceAffineCoordinates_full_outer_degree
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).natDegree = f.totalDegree := by
  have hc :
      (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree ≠ 0 := by
    simp_all [hypersurfaceAffineCoordinates_top_coefficient]
  grind [le_antisymm, natDegree_optionEquivLeft, degreeOf_le_totalDegree, hypersurfaceAffineCoordinates_totalDegree_le, Polynomial.le_natDegree_of_ne_zero]

end
end CCDN
