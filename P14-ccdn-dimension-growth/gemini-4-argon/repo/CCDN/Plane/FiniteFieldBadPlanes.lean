/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Plane.FiniteFieldPolynomialZeros

/-! Counting all affine-plane parameter choices whose section drops degree
or is not geometrically irreducible. This includes zero restrictions, but
incidence averaging uses a sharper separate bound on those. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The bivariate restriction at a point of the full parameter space. -/
def universalPlaneSection {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) : Polynomial (Polynomial K) :=
  bivariateMap (eval v) (universalPlanePolynomial f)

/-- The plane parameters (possibly degenerate) at which the plane section of `f` drops total degree
or is not geometrically irreducible. -/
def BadPlaneParameters {K σ : Type*} [Field K] (f : MvPolynomial σ K) :=
  {v : PlaneParameters σ → K //
    bivariateTotalDegree (universalPlaneSection f v) ≠ f.totalDegree ∨
      ¬Irreducible (bivariateMap (algebraMap K (AlgebraicClosure K)) (universalPlaneSection f v))}

/-- Mapping the coefficients of a nested bivariate polynomial along a composite ring
homomorphism `ψ.comp φ` is the same as mapping along `φ` and then along `ψ`. -/
lemma bivariateMap_comp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (f : Polynomial (Polynomial R)) :
    bivariateMap (ψ.comp φ) f = bivariateMap ψ (bivariateMap φ f) := by
  ext i j
  simp only [bivariateMap_coeff, RingHom.comp_apply]

/-- In m ambient coordinates, at most 2*d^3*q^(3*m-1) parameter choices
are bad. This counts triples (base point, first direction, second direction). -/
theorem finite_field_bad_plane_parameters_card
    {K σ : Type*} [Field K] [Fintype K] [Fintype σ] {p : ℕ} [CharP K p]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : 2 * f.totalDegree ^ 2 < p) :
    Nat.card (BadPlaneParameters f) ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ (3 * (Fintype.card σ + 1) - 1) := by
  classical
  obtain ⟨rows, cols, hw, hdeg⟩ := exists_universalPlane_badWitness f hf hpos (.of_charP hchar)
  let W := universalPlaneBadWitness f rows cols
  have hdp : f.totalDegree < p := by nlinarith
  let ψ : BadPlaneParameters f → {v : PlaneParameters (Option σ) → K // eval v W = 0} :=
    fun v => ⟨v.val, by
      by_contra h
      have hbase := universalPlaneBadWitness_good_specialization f hpos (.of_charP hdp) rows cols
        (eval v.val) h
      rcases v.property with hdeg' | hir
      · exact hdeg' hbase.2.1
      · let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
        have hw' : (φ.comp (eval v.val)) W ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr h
        have hh := universalPlaneBadWitness_good_specialization f hpos
          ((CharZeroOrGT.of_charP hdp).map φ) rows cols _ hw'
        exact hir (by simpa only [bivariateMap_comp_apply, universalPlaneSection, φ] using hh.2.2)⟩
  have hψ : Function.Injective ψ := fun x y h =>
    Subtype.ext (congrArg (fun z : {v : PlaneParameters (Option σ) → K // eval v W = 0} => z.val) h)
  have h := ((Nat.mul_le_mul_right (Fintype.card K)
    (Nat.card_le_card_of_injective ψ hψ)).trans (finite_field_polynomial_zeros_mul_card W hw)).trans
    (Nat.mul_le_mul_right _ hdeg)
  have hN : 1 ≤ Fintype.card (PlaneParameters (Option σ)) := Fintype.card_pos
  have he : Fintype.card K ^ Fintype.card (PlaneParameters (Option σ)) =
      Fintype.card K ^ (Fintype.card (PlaneParameters (Option σ)) - 1) * Fintype.card K := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [he, ← Nat.mul_assoc] at h
  have hc : Nat.card (BadPlaneParameters f) ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ (Fintype.card (PlaneParameters (Option σ)) - 1) :=
    Nat.le_of_mul_le_mul_right h Fintype.card_pos
  simpa [PlaneParameters, Nat.mul_comm] using hc

end
end CCDN
