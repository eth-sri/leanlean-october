/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerGenericFactors
import CCDN.ForMathlib.Matrix
import CCDN.Noether.EulerPairSpecialization

/-!
Characteristic-independent vanishing on products. A generic integral
identity is proved in the fraction field and then specialized; this includes
inseparable and repeated factors in every characteristic.

A nonzero Euler kernel vector forces every maximal universal
coefficient minor to vanish after specialization.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Polynomial Module

/-- Every maximal Euler minor vanishes on a product with two positive
degree budgets, over an arbitrary commutative coefficient ring. -/
theorem eulerClosedForm_minor_eq_zero_of_product
    {R : Type*} [CommRing R] (k a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : R[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (g * h)).submatrix rows cols).det = 0 := by
  classical
  let P := MvPolynomial (EulerFactorParameters a b) ℤ
  let F := FractionRing P
  let φ := algebraMap P F
  let G := genericEulerFactorLeft a b
  let H := genericEulerFactorRight a b
  have hφ := IsFractionRing.injective P F
  have hmap : Function.Injective (bivariateMap φ) :=
    Polynomial.map_injective _ (Polynomial.map_injective φ hφ)
  have hne : eulerFactorPair a b (bivariateMap φ G) (bivariateMap φ H) ≠ 0 := fun hz => by
    have he := eulerFactorPair_map φ a b G H
    rw [hz] at he
    exact genericEulerFactorPair_ne_zero a b ha hb <| Prod.ext
      (hmap (by simpa only [Prod.fst_zero, map_zero] using congrArg Prod.fst he))
      (hmap (by simpa only [Prod.snd_zero, map_zero] using congrArg Prod.snd he))
  obtain ⟨u, hu, hk⟩ := exists_eulerFactorKernel k a b ha hb hab
    (bivariateMap φ G) (bivariateMap φ H)
    ((bivariateTotalDegree_map_le φ G).trans (eulerPolynomialFromCoefficients_degree a _))
    ((bivariateTotalDegree_map_le φ H).trans (eulerPolynomialFromCoefficients_degree b _)) hne
  have hgen : ((eulerClosedFormCoefficientMatrix k (G * H)).submatrix rows cols).det = 0 := by
    apply hφ
    rw [map_zero, eulerClosedForm_minor_map, map_mul]
    by_contra hdet
    let A := eulerClosedFormCoefficientMatrix k (bivariateMap φ G * bivariateMap φ H)
    have hlo : (k + 2) ^ 2 - 1 ≤ A.rank := A.le_rank_of_det_submatrix_ne_zero rows cols hdet
    have hr : A.rank = Fintype.card (EulerColumns k) :=
      le_antisymm (Matrix.rank_le_card_width _) (by simpa only [card_eulerColumns] using hlo)
    have hi : LinearIndependent F A.col := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← Matrix.rank_eq_finrank_span_cols, hr]
    let T := (bivariateCoefficients F).comp
      (eulerClosedFormOperator k (bivariateMap φ G * bivariateMap φ H))
    have hsum : ∑ i, (eulerPairBasis F k).repr u i • A.col i = 0 := by
      have hh := congrArg T ((eulerPairBasis F k).sum_repr u)
      rw [map_sum] at hh
      simp only [map_smul] at hh
      change (∑ i, (eulerPairBasis F k).repr u i • A.col i) =
        bivariateCoefficients F (eulerClosedFormOperator k _ u) at hh
      rwa [hk, map_zero] at hh
    have hz := Fintype.linearIndependent_iff.mp hi _ hsum
    exact hu ((eulerPairBasis F k).repr.injective <| Finsupp.ext fun i => by
      simpa only [map_zero, Finsupp.zero_apply] using hz i)
  have hz := congrArg (genericEulerFactorSpecialization a b g h) hgen
  rwa [map_zero, eulerClosedForm_minor_map, map_mul,
    genericEulerFactorLeft_specialize a b g h hg,
    genericEulerFactorRight_specialize a b g h hh] at hz

end
end CCDN
