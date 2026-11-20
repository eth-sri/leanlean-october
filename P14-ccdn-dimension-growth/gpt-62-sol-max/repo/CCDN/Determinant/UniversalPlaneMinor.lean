/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfacePositioning
public import CCDN.Determinant.GenericPlaneSmoothness
public import CCDN.Noether.UniversalPlane
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Noether.ClosedFormScaling
import CCDN.Noether.ShearNormalization

/-! The constructed positioned family is a specialization of the universal
family of all affine planes. Its nonzero minor therefore proves that a
universal parameter polynomial is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The second direction has zero first coordinate and generic transverse slopes. -/
def genericTransverseDirection (K F σ : Type*) [Field K] [CommRing F]
    [Algebra (MvPolynomial σ K) F] : Option σ → F :=
  fun i => Option.elim i 0 (fun j => algebraMap (MvPolynomial σ K) F (X j))

section

variable {K F σ : Type*} [Field K] [CommRing F]
  [Algebra K F] [Algebra (MvPolynomial σ K) F]
include K F σ

private lemma genericPlaneMap_affineCoordinates
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    genericPlaneMap K F σ (hypersurfaceAffineCoordinates a b hb f) =
      MvPolynomial.map (planeParameterEval (algebraMap K F)
        (algebraMap K F ∘ a) (algebraMap K F ∘ b) (genericTransverseDirection K F σ))
        (universalPlaneMap K (Option σ) f) := by
  rw [universalPlaneMap_specialize]
  let φ := (genericPlaneMap K F σ).toRingHom.comp
    (hypersurfaceAffineCoordinates a b hb).toRingHom
  refine RingHom.congr_fun (f := φ) ?_ f
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [φ, genericPlaneMap]
  · intro i
    cases i <;> simp [φ, hypersurfaceAffineCoordinates_X, genericPlaneMap,
      genericTransverseDirection]

/-- Monic normalization changes the specialized equation only by a scalar. -/
lemma normalized_genericPlane_universal_specialization
    [IsScalarTower K (MvPolynomial σ K) F]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    bivariateMap (algebraMap (MvPolynomial σ K) F)
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f)) =
      algebraMap K F (eval b (homogeneousComponent f.totalDegree f))⁻¹ •
        bivariateMap (planeParameterEval (algebraMap K F)
          (algebraMap K F ∘ a) (algebraMap K F ∘ b) (genericTransverseDirection K F σ))
          (universalPlanePolynomial f) := by
  rw [← genericPlaneMap_bivariate, normalizedHypersurfaceCoordinates, map_mul,
    genericPlaneMap_affineCoordinates, map_mul]
  rw [bivariate_smul_eq_constant_mul, universalPlanePolynomial, bivariatePolynomialEquiv_map]
  simp [bivariatePolynomialEquiv_C]

end

/-- Every irreducible positive-degree hypersurface over an algebraically closed
field of characteristic zero or >2*d^2 has a nonzero minor in the UNIVERSAL affine-plane
parameter ring, not merely in a family through a fixed line. -/
theorem exists_universalPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    (closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).HasNonzeroMinor
      (2 * f.totalDegree ^ 2 - 1) := by
  obtain ⟨a, b, hb, rows, cols, hdet⟩ :=
    exists_positioned_genericPlane_minor f hf hpos hchar
  let R := MvPolynomial σ K
  have he := normalized_genericPlane_universal_specialization (F := R) a b hb f
  rw [show algebraMap R R = RingHom.id R from Algebra.algebraMap_self,
    show ∀ q : Polynomial (Polynomial R), bivariateMap (RingHom.id R) q = q from
      fun q => by ext i j; simp] at he
  rw [he, closedForm_minor_smul, ← closedForm_minor_map] at hdet
  refine ⟨rows, cols, fun hz => hdet ?_⟩
  rw [hz, map_zero, mul_zero]

end
end CCDN
