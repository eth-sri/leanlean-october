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

section

variable {K σ : Type*}

/-- The bivariate restriction at a point of the full parameter space. -/
def universalPlaneSection [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) : Polynomial (Polynomial K) :=
  bivariateMap (eval v) (universalPlanePolynomial f)

/-- The plane parameters (possibly degenerate) at which the plane section of `f` drops total degree
or is not geometrically irreducible. -/
def BadPlaneParameters [Field K] (f : MvPolynomial σ K) :=
  {v : PlaneParameters σ → K //
    bivariateTotalDegree (universalPlaneSection f v) ≠ f.totalDegree ∨
      ¬Irreducible (bivariateMap (algebraMap K (AlgebraicClosure K)) (universalPlaneSection f v))}

/-- Mapping the coefficients of a nested bivariate polynomial along a composite ring
homomorphism `ψ.comp φ` is the same as mapping along `φ` and then along `ψ`. -/
lemma bivariateMap_comp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (f : Polynomial (Polynomial R)) :
    bivariateMap (ψ.comp φ) f = bivariateMap ψ (bivariateMap φ f) := by
  aesop

private lemma badPlaneParameters_witness_zero [Field K] {p : ℕ} [CharP K p]
    (f : MvPolynomial σ K) (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : BadPlaneParameters f) : eval v.val (universalPlaneBadWitness f rows cols) = 0 := by
  by_contra h
  have hbase := universalPlaneBadWitness_good_specialization f hpos (.of_charP hchar) rows cols
    _ h
  rcases v.property with hdeg | hir
  · exact hdeg hbase.2.1
  · let φ := algebraMap K (AlgebraicClosure K)
    have hw : (φ.comp _) _ ≠ 0 :=
      (map_ne_zero_iff φ φ.injective).mpr h
    have hh := universalPlaneBadWitness_good_specialization f hpos
      ((CharZeroOrGT.of_charP hchar).map φ) rows cols _ hw
    simp_all [bivariateMap_comp_apply, universalPlaneSection, φ]

end

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] {p : ℕ} [CharP K p]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : 2 * f.totalDegree ^ 2 < p)

include hf hpos hchar in
/-- The proportion of geometrically bad plane parameters is at most 2*d^3/q. -/
private theorem finite_field_bad_plane_parameters_mul_card :
    Nat.card (BadPlaneParameters f) * Fintype.card K ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ Fintype.card (PlaneParameters (Option σ)) := by
  classical
  obtain ⟨rows, cols, hw, hdeg⟩ := exists_universalPlane_badWitness f hf hpos
    (.of_charP hchar)
  let W := universalPlaneBadWitness f rows cols
  have hdp : f.totalDegree < p := by nlinarith
  let ψ : BadPlaneParameters f → {v : PlaneParameters _ → K // eval v W = 0} :=
    fun v => ⟨v.val, badPlaneParameters_witness_zero f hpos hdp rows cols v⟩
  have hψ : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    grind
  exact ((Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective ψ hψ)).trans (finite_field_polynomial_zeros_mul_card W hw)).trans
    (Nat.mul_le_mul_right _ hdeg)

include hf hpos hchar in
/-- In m ambient coordinates, at most 2*d^3*q^(3*m-1) parameter choices
are bad. This counts triples (base point, first direction, second direction). -/
theorem finite_field_bad_plane_parameters_card :
    Nat.card (BadPlaneParameters f) ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ (3 * (Fintype.card σ + 1) - 1) := by
  have h := finite_field_bad_plane_parameters_mul_card f hf hpos hchar
  have he : Fintype.card K ^ Fintype.card (PlaneParameters (Option σ)) =
      Fintype.card K ^ (Fintype.card (PlaneParameters (Option σ)) - 1) * Fintype.card K := by
    simp
  rw [he, ← Nat.mul_assoc] at h
  simpa [Nat.mul_comm] using (Nat.le_of_mul_le_mul_right h Fintype.card_pos)

end
end CCDN
