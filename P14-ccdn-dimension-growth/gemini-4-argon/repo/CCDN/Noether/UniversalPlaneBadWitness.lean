/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalPlaneWitness
import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.ClosedFormScaling

/-! A nonzero polynomial of degree at most 2*d^3 detects all plane sections
that lose the full degree or fail geometric irreducibility. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The universal plane restriction of `f` has total degree at most the total degree of `f` in the
two plane coordinates. -/
lemma universalPlaneMap_planeDegree_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) : (universalPlaneMap K σ f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom (C.comp (C : K →+* MvPolynomial (PlaneParameters σ) K))
    (fun i => C (X (i, 0)) + C (X (i, 1)) * X 0 + C (X (i, 2)) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le
  intro i
  have hx (j : Fin 2) :
      (X j : MvPolynomial (Fin 2) (MvPolynomial (PlaneParameters σ) K)).totalDegree ≤ 1 := by
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : MvPolynomial (PlaneParameters σ) K)
  exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
    (max_le (by simp) ((totalDegree_mul _ _).trans (by simpa using hx 0))))
    ((totalDegree_mul _ _).trans (by simpa using hx 1)))

/-- Every specialization of the plane parameters of the universal plane restriction of `f` has
total degree at most the total degree of `f`. -/
lemma universalPlanePolynomial_specialization_totalDegree {K L σ : Type*}
    [CommRing K] [CommRing L] (f : MvPolynomial σ K)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L) :
    bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) ≤ f.totalDegree :=
  (bivariateTotalDegree_map_le φ _).trans
    (by simpa only [universalPlanePolynomial, bivariateTotalDegree, AlgEquiv.symm_apply_apply]
      using universalPlaneMap_planeDegree_le f)

/-- The bad-plane witness: the universal outer leading coefficient of the plane restriction of
`f` times the closed-form minor with rows `rows` and columns `cols`. The leading-coefficient
factor detects all outer-degree drops. -/
def universalPlaneBadWitness {K σ : Type*} [CommRing K] (f : MvPolynomial σ K)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree) :
    MvPolynomial (PlaneParameters σ) K :=
  universalPlaneLeading f *
    ((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix
      rows cols).det

private lemma universalPlaneBadWitness_degree {K σ : Type*} [CommRing K] (f : MvPolynomial σ K)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree) :
    (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  refine (totalDegree_mul _ _).trans
    ((Nat.add_le_add (universalPlanePolynomial_coefficient_degree f f.totalDegree 0)
      (closedForm_minor_parameterDegree _ _ _ _
        (universalPlanePolynomial_coefficient_degree f) rows cols)).trans ?_)
  rcases eq_or_ne f.totalDegree 0 with h | h
  · simp [h]
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ 2 * f.totalDegree ^ 2 by
      have := Nat.pos_of_ne_zero h; nlinarith)]

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
    (bivariateMap φ (universalPlanePolynomial f)).natDegree = f.totalDegree ∧
      bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) = f.totalDegree ∧
      Irreducible (bivariateMap φ (universalPlanePolynomial f)) := by
  let g := bivariateMap φ (universalPlanePolynomial f)
  have hh := mul_ne_zero_iff.mp (by simpa only [universalPlaneBadWitness, map_mul] using hw)
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f φ
  have hc : (g.coeff f.totalDegree).coeff 0 ≠ 0 := by
    simpa only [g, bivariateMap_coeff, universalPlaneLeading] using hh.1
  have hd : g.natDegree = f.totalDegree :=
    le_antisymm ((bivariate_natDegree_le_totalDegree g).trans ht)
      (Polynomial.le_natDegree_of_ne_zero fun hz => hc (by rw [hz, Polynomial.coeff_zero]))
  refine ⟨hd, le_antisymm ht (hd ▸ bivariate_natDegree_le_totalDegree g), ?_⟩
  by_contra hred
  have hl : g.leadingCoeff = Polynomial.C (φ (universalPlaneLeading f)) := by
    rw [bivariate_leadingCoeff_eq_constant g (by omega)]
    exact congrArg Polynomial.C
      (by change (g.coeff g.natDegree).coeff 0 = _; rw [hd]; exact bivariateMap_coeff φ _ _ _)
  have hr := closedForm_rank_drop_of_constant_leading f.totalDegree hpos hchar _ hh.1 g hl hred hd ht
  have hrank : _ ≤ (closedFormCoefficientMatrix f.totalDegree g).rank :=
    Matrix.le_rank_of_det_submatrix_ne_zero _ rows cols (by rw [← closedForm_minor_map]; exact hh.2)
  omega

/-- A concrete cubic-degree bad-section witness over the original field. -/
theorem exists_universalPlane_badWitness
    {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      universalPlaneBadWitness f rows cols ≠ 0 ∧
      (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  obtain ⟨rows, cols, hdet, _⟩ := exists_universalPlane_minor_degree f hf hpos hchar
  exact ⟨rows, cols,
    mul_ne_zero (universalPlaneLeading_ne_zero f hf hpos
      (hchar.mono (by nlinarith [Nat.le_mul_self f.totalDegree]))) hdet,
    universalPlaneBadWitness_degree f rows cols⟩

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
  have hex := exists_universalPlane_minor (MvPolynomial.map φ f) hf (ht ▸ hpos) (.of_charZero _)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  have hm : ((closedFormCoefficientMatrix f.totalDegree
      (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 :=
    fun he => hdet (by rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero])
  have hl : universalPlaneLeading f ≠ 0 := by
    have hn := universalPlaneLeading_ne_zero_of_irreducible (MvPolynomial.map φ f) hf
      (ht ▸ hpos) (.of_charZero _)
    rw [show universalPlaneLeading (MvPolynomial.map φ f) =
      MvPolynomial.map φ (universalPlaneLeading f) by
      simp only [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]] at hn
    exact fun hz => hn (by rw [hz, map_zero])
  exact ⟨rows, cols, mul_ne_zero hl hm, universalPlaneBadWitness_degree f rows cols⟩

end
end CCDN
