/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.AffineTranslation
import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.AuxiliaryPolynomial.AffineLeadingTranslation

/-! Parallel affine slices preserve the good leading hyperplane section.
Rational restriction equations can then be replaced by integer
polynomials without changing their zero sets or total degrees. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [CommRing K] {n : ℕ}

/-- The `K`-algebra automorphism of `K[x_none, x_0, …, x_{n-1}]` translating the distinguished
coordinate `x_none` by the constant `c` and fixing the other coordinates. -/
def optionCoordinateShift (c : K) :
    MvPolynomial (Option (Fin n)) K →ₐ[K] MvPolynomial (Option (Fin n)) K :=
  aeval (fun i => Option.elim i (X none + C c) (fun j => X (some j)))

lemma optionCoordinateShift_rename
    (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    rename (finSuccEquiv n).symm (optionCoordinateShift c f) =
      affineTranslation K (Fin.cons c (fun _ => 0)) (rename (finSuccEquiv n).symm f) := by
  have he : (rename (finSuccEquiv n).symm).toRingHom.comp (optionCoordinateShift c).toRingHom =
      (affineTranslation K (Fin.cons c (fun _ => 0))).toRingHom.comp
        (rename (finSuccEquiv n).symm).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [optionCoordinateShift, affineTranslation]
    · intro i
      cases i <;> simp [optionCoordinateShift, affineTranslation]
  exact RingHom.congr_fun he f

lemma optionCoordinateShift_top [Nontrivial K]
    (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    homogeneousComponent f.totalDegree (optionCoordinateShift c f) =
      homogeneousComponent f.totalDegree f := by
  apply rename_injective (finSuccEquiv n).symm (finSuccEquiv n).symm.injective
  rw [rename_homogeneousComponent, optionCoordinateShift_rename, rename_homogeneousComponent]
  simpa [affineTranslation_totalDegree, ← renameEquiv_apply, totalDegree_renameEquiv] using
    affineTranslation_leading_homogeneousComponent (Fin.cons c (fun _ => 0))
      (rename (finSuccEquiv n).symm f)

lemma optionCoordinateShift_eval
    (c : K) (x : Option (Fin n) → K) (f : MvPolynomial (Option (Fin n)) K) :
    eval x (optionCoordinateShift c f) =
      eval (fun i => Option.elim i (x none + c) (fun j => x (some j))) f := by
  have he : (eval x).comp (optionCoordinateShift c).toRingHom =
      eval (fun i => Option.elim i (x none + c) (fun j => x (some j))) := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      cases i <;> simp [optionCoordinateShift]
  exact RingHom.congr_fun he f

end

section
variable {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K)

/-- The restriction of `f` to the affine hyperplane `x_none = ∑ a j * x j + c`, written as a
polynomial in the remaining coordinates `x j`. -/
def affineGraphHyperplaneSlice
    :
    MvPolynomial (Fin n) K :=
  graphHyperplaneRestriction a (optionCoordinateShift c f)

/-- Evaluating the affine slice `affineGraphHyperplaneSlice a c f` at `x` is evaluating `f` at the
point of the hyperplane `x_none = ∑ a j * x j + c` lying over `x`. -/
lemma affineGraphHyperplaneSlice_eval
    (x : Fin n → K) :
    eval x (affineGraphHyperplaneSlice a c f) =
      eval (fun i => Option.elim i ((∑ j, a j * x j) + c) x) f := by
  rw [affineGraphHyperplaneSlice, graphHyperplaneRestriction_eval, optionCoordinateShift_eval]
  rfl

end

variable {K : Type*} {n : ℕ}

/-- The degree-`f.totalDegree` component of an affine slice of `f` is the restriction of the top
form of `f` to the parallel linear hyperplane `x_none = ∑ a j * x j`. -/
lemma affineGraphHyperplaneSlice_top [CommRing K] [Nontrivial K]
    (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    homogeneousComponent f.totalDegree (affineGraphHyperplaneSlice a c f) =
      graphHyperplaneRestriction a (homogeneousComponent f.totalDegree f) := by
  rw [affineGraphHyperplaneSlice, ← graphHyperplaneRestriction_homogeneousComponent,
    optionCoordinateShift_top]

