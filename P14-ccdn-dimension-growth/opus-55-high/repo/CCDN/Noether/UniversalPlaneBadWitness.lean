/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.UniversalPlaneWitness
import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.ClosedFormScaling

/-! A nonzero polynomial of degree at most 2*d^3 detects all plane sections
that lose the full degree or fail geometric irreducibility. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The universal plane restriction of `f` has total degree at most the total degree of `f` in the
two plane coordinates. -/
lemma universalPlaneMap_planeDegree_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) : (universalPlaneMap K σ f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom (C.comp C)
    (fun i => C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le
  intro i
  have hx (j : Fin 2) :
      (X j : MvPolynomial (Fin 2) (MvPolynomial (PlaneParameters σ) K)).totalDegree ≤ 1 := by
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : MvPolynomial (PlaneParameters σ) K)
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp_all)
  · exact (totalDegree_mul _ _).trans (by simp_all)

/-- Every specialization of the plane parameters of the universal plane restriction of `f` has
total degree at most the total degree of `f`. -/
lemma universalPlanePolynomial_specialization_totalDegree {K L σ : Type*}
    [CommRing K] [CommRing L] (f : MvPolynomial σ K)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L) :
    bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) ≤ f.totalDegree := by
  apply (bivariateTotalDegree_map_le φ _).trans
  simpa [universalPlanePolynomial, bivariateTotalDegree, AlgEquiv.symm_apply_apply]
    using universalPlaneMap_planeDegree_le f

section
variable {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ) (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)

/-- The bad-plane witness: the universal outer leading coefficient of the plane restriction of
`f` times the closed-form minor with rows `rows` and columns `cols`. The leading-coefficient
factor detects all outer-degree drops. -/
def universalPlaneBadWitness
    :
    MvPolynomial (PlaneParameters σ) K :=
  universalPlaneLeading f *
    ((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix
      rows cols).det

lemma universalPlaneBadWitness_degree
    :
    (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  apply (totalDegree_mul _ _).trans
  have hl := universalPlanePolynomial_coefficient_degree f f.totalDegree 0
  have hm := closedForm_minor_parameterDegree _ _ _ _
    (universalPlanePolynomial_coefficient_degree f) rows cols
  calc
    _ ≤ f.totalDegree + (2 * f.totalDegree ^ 2 - 1) * f.totalDegree := Nat.add_le_add hl hm
    _ ≤ 2 * f.totalDegree ^ 3 := by
      by_cases h : f.totalDegree = 0
      · grind
      · have h1 : 1 ≤ 2 * f.totalDegree ^ 2 := by
          have : 0 < f.totalDegree := Nat.pos_of_ne_zero h; nlinarith
        have he := Nat.sub_add_cancel h1
        nlinarith

end

/-- Nonvanishing certifies full degree and irreducibility over ANY target
field of characteristic zero or greater than d. In particular it applies in the
algebraic closure when detecting geometrically bad finite-field planes. -/
theorem universalPlaneBadWitness_good_specialization
    {K L σ : Type*} [CommRing K] [Field L]
    (f : MvPolynomial σ K) (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT L f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L)
    (hw : φ (universalPlaneBadWitness f rows cols) ≠ 0) :
    bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) = f.totalDegree ∧
      Irreducible (bivariateMap φ (universalPlanePolynomial f)) := by
  let g := bivariateMap φ (universalPlanePolynomial f)
  have hh := mul_ne_zero_iff.mp (show φ (universalPlaneLeading f) *
      φ (((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix
        rows cols).det) ≠ 0
      by simp_all [universalPlaneBadWitness, map_mul])
  have ht :=
    universalPlanePolynomial_specialization_totalDegree f φ
  have hc : ((g.coeff f.totalDegree).coeff 0) ≠ 0 := by aesop
  have hd : g.natDegree = f.totalDegree := by
    apply le_antisymm ((bivariate_natDegree_le_totalDegree g).trans ht)
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    simp_all
  have he : bivariateTotalDegree g = f.totalDegree :=
    ht.antisymm (hd ▸ bivariate_natDegree_le_totalDegree g)
  refine ⟨he, ?_⟩
  by_contra hred
  have hl : g.leadingCoeff = Polynomial.C (φ (universalPlaneLeading f)) := by
    rw [bivariate_leadingCoeff_eq_constant g (by omega)]
    congr 1
    change (g.coeff g.natDegree).coeff 0 = _
    aesop
  have hr := closedForm_rank_drop_of_constant_leading f.totalDegree hpos hchar
    _ hh.1 g hl hred hd ht
  have hdet : ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det ≠ 0 := by
    rw [← closedForm_minor_map]
    exact hh.2
  have hrank := Matrix.le_rank_of_det_submatrix_ne_zero _ rows cols hdet
  omega

/-- A nonzero integer polynomial in the full parameter space,
constructed for every geometrically irreducible integer equation. -/
theorem exists_integer_universalPlane_badWitness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      universalPlaneBadWitness f rows cols ≠ 0 ∧
      (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  let φ : ℤ →+* L := Int.castRingHom L
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective (RingHom.injective_int _) f
  have hex := exists_universalPlane_minor (MvPolynomial.map φ f) hf (ht ▸ hpos)
    (.of_charZero _)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  have hm : ((closedFormCoefficientMatrix f.totalDegree
      (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 := by
    intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  exact ⟨rows, cols, mul_ne_zero (by
    have hn := universalPlaneLeading_ne_zero_of_irreducible (MvPolynomial.map φ f) hf
      (ht ▸ hpos) (.of_charZero _)
    have he : universalPlaneLeading (MvPolynomial.map φ f) =
        MvPolynomial.map φ (universalPlaneLeading f) := by
      simp [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]
    grind) hm, universalPlaneBadWitness_degree f rows cols⟩

