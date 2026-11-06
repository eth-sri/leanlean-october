/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Plane.FiniteFieldPolynomialZeros

/-! Counting all affine-plane parameter choices whose section drops degree
or is not geometrically irreducible. This includes zero restrictions, but
incidence averaging uses a sharper separate bound on those. -/

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

end

/-- Mapping the coefficients of a nested bivariate polynomial along a composite ring
homomorphism `ψ.comp φ` is the same as mapping along `φ` and then along `ψ`. -/
lemma bivariateMap_comp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (f : Polynomial (Polynomial R)) :
    bivariateMap (ψ.comp φ) f = bivariateMap ψ (bivariateMap φ f) := by
  ext i j
  simp

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] {p : ℕ} [CharP K p] (f : MvPolynomial (Option σ) K) (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) (hpos : 0 < f.totalDegree) (hchar : 2 * f.totalDegree ^ 2 < p)
include hf hpos hchar

/-- The proportion of geometrically bad plane parameters is at most 2*d^3/q. -/
theorem finite_field_bad_plane_parameters_mul_card
    :
    Nat.card (BadPlaneParameters f) * Fintype.card K ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ Fintype.card (PlaneParameters (Option σ)) := by
  have hc : CharZeroOrGT K (2 * f.totalDegree ^ 2) := .of_charP hchar
  let φ := algebraMap K (AlgebraicClosure K)
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective φ.injective _
  have hex := exists_universalPlane_minor (MvPolynomial.map φ f) hf (ht ▸ hpos) (ht ▸ hc.map φ)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  have hw : universalPlaneBadWitness f rows cols ≠ 0 := mul_ne_zero
    (show universalPlaneLeading f ≠ 0 by
        let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
        have hn := universalPlaneLeading_ne_zero_of_irreducible (MvPolynomial.map φ f) hf (ht ▸ hpos)
          (ht ▸ (hc.mono (by nlinarith)).map φ)
        rw [universalPlaneLeading_map] at hn
        exact fun hz ↦ hn (by grind)) fun he => by
      rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
      grind
  have hdeg := universalPlaneBadWitness_degree f rows cols
  let W := universalPlaneBadWitness f rows cols
  have hdp : f.totalDegree < p := by nlinarith
  let ψ : BadPlaneParameters f → {v : PlaneParameters (Option σ) → K // eval v W = 0} :=
    fun v => ⟨v.val, (show eval v.val (universalPlaneBadWitness f rows cols) = 0 by
        by_contra h
        have hbase := universalPlaneBadWitness_good_specialization f hpos (.of_charP hdp) rows cols
          (eval v.val) h
        rcases v.property with hdeg | hir
        · exact hdeg hbase.1
        · let L := AlgebraicClosure K
          let φ : K →+* L := algebraMap K L
          have hw : (φ.comp (eval v.val)) (universalPlaneBadWitness f rows cols) ≠ 0 :=
            (map_ne_zero_iff φ φ.injective).mpr h
          have hh := universalPlaneBadWitness_good_specialization f hpos
            ((CharZeroOrGT.of_charP hdp).map φ) rows cols _ hw
          apply hir
          simpa [bivariateMap_comp_apply, universalPlaneSection, φ] using hh.2)⟩
  have hcard := Nat.card_le_card_of_injective ψ (by
    intro x y h
    apply Subtype.ext
    grind)
  have hb := finite_field_polynomial_zeros_mul_card W hw
  exact ((Nat.mul_le_mul_right (Fintype.card K) hcard).trans hb).trans
    (Nat.mul_le_mul_right _ hdeg)

/-- In m ambient coordinates, at most 2*d^3*q^(3*m-1) parameter choices
are bad. This counts triples (base point, first direction, second direction). -/
theorem finite_field_bad_plane_parameters_card
    :
    Nat.card (BadPlaneParameters f) ≤
      (2 * f.totalDegree ^ 3) * Fintype.card K ^ (3 * (Fintype.card σ + 1) - 1) := by
  have h := finite_field_bad_plane_parameters_mul_card f hf hpos hchar
  have hN : 1 ≤ Fintype.card (PlaneParameters (Option σ)) := Fintype.card_pos
  have he : Fintype.card K ^ Fintype.card (PlaneParameters (Option σ)) =
      Fintype.card K ^ (Fintype.card (PlaneParameters (Option σ)) - 1) * Fintype.card K := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [he, ← Nat.mul_assoc] at h
  have hc :=
    Nat.le_of_mul_le_mul_right h Fintype.card_pos
  simpa [PlaneParameters, Nat.mul_comm] using hc

