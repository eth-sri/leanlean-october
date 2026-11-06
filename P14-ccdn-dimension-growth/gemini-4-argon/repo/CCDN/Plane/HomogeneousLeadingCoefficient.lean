/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousChart
import CCDN.Plane.GridHeight

/-! Positioning a coefficient-height witness as the lexicographic leading
coefficient by a bounded integral translation of the affine chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped MonomialOrder

/- Every exponent of total degree at most `d` is lexicographically at most the pure power
`x₀ ^ d` of the first variable. -/

/-- If `f` has total degree at most `d` and a nonzero coefficient at `x₀ ^ d`, then its
lexicographic leading coefficient is that coefficient. -/
lemma lex_leadingCoeff_eq_pure_first {R : Type*} [CommRing R] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) R) (hd : f.totalDegree ≤ d)
    (hc : f.coeff (Finsupp.single 0 d) ≠ 0) :
    MonomialOrder.lex.leadingCoeff f = f.coeff (Finsupp.single 0 d) := by
  have he : MonomialOrder.lex.degree f = Finsupp.single 0 d := by
    apply MonomialOrder.lex.toSyn.injective
    refine le_antisymm (MonomialOrder.degree_le_iff.mpr fun m hm => ?_)
      (MonomialOrder.lex.le_degree (mem_support_iff.mpr hc))
    have hmd := (le_totalDegree hm).trans hd
    have hs := exponent_degree_split m
    by_cases he0 : m 0 = d
    · have ht : chartExponent m = 0 := (Finsupp.degree_eq_zero_iff _).mp
        (by change (chartExponent m).sum (fun _ e => e) = 0; omega)
      rw [show m = Finsupp.single 0 d by
        ext i; refine Fin.cases (by simpa using he0) (fun j => ?_) i
        simpa only [chartExponent_apply, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.single_eq_of_ne (Fin.succ_ne_zero j)] using congrArg (fun t => t j) ht]
    · apply le_of_lt
      change toLex m < toLex (Finsupp.single (0 : Fin (n + 1)) d)
      exact ⟨0, fun i hi => (not_lt_of_ge (Fin.zero_le i) hi).elim,
        by simp only [ofLex_toLex, Finsupp.single_eq_same]; omega⟩
  change f.coeff (MonomialOrder.lex.degree f) = _
  rw [he]

/-- For `f` homogeneous of degree `d`, the coefficient of `x₀ ^ d` in the translate
`homogeneousTranslation R a f` is the value `f (1, a)`. -/
lemma homogeneousTranslation_pure_first {R : Type*} [CommRing R] {n d : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) (hf : f.IsHomogeneous d) :
    (homogeneousTranslation R a f).coeff (Finsupp.single 0 d) = eval (Fin.cons 1 a) f := by
  let g := homogeneousTranslation R a f
  have hg : g.IsHomogeneous d := homogeneousTranslation_homogeneous a hf
  obtain ⟨j, hj⟩ := homogeneousMonomials_surjective n d (Finsupp.single 0 d) (by simp)
  have hc := affineChart_homogeneous_coefficient g hg j
  rw [hj, show chartExponent (Finsupp.single (0 : Fin (n + 1)) d) = 0 by
    ext i; simp [chartExponent_apply]] at hc
  rw [← hc, ← constantCoeff_eq, ← eval_zero, affineChart_eval,
    homogeneousTranslation_eval_chart, zero_add]

/-- Every original coefficient is controlled by the leading coefficient
obtained by a translation with parameters in 0,...,d. -/
theorem exists_bounded_leading_coefficient_translation {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin 2 → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) ≠ 0 ∧
      CoefficientHeightLE f (((d : ℝ) + 1) ^ (2 * (d + 1)) *
        |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|) := by
  have hc0 : affineChart 2 f ≠ 0 := fun hz =>
    hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
      (by simpa only [map_zero] using hz))
  obtain ⟨x, y, hx, hy, hval, hcoeff⟩ := exists_integer_plane_grid_height_witness (affineChart 2 f)
    hc0 ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  let a : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  have he : (homogeneousTranslation ℤ a f).coeff (Finsupp.single 0 d) =
      eval ![(x : ℤ), (y : ℤ)] (affineChart 2 f) := by
    rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
  have hlc := lex_leadingCoeff_eq_pure_first (homogeneousTranslation ℤ a f)
    (homogeneousTranslation_homogeneous a hf).totalDegree_le (he ▸ hval)
  refine ⟨a, fun j => ?_, by rw [hlc, he]; exact hval, fun m => ?_⟩
  · fin_cases j <;> dsimp [a]
    · exact ⟨by positivity, mod_cast hx⟩
    · exact ⟨by positivity, mod_cast hy⟩
  · by_cases hm : m.degree = d
    · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective 2 d m hm
      rw [← affineChart_homogeneous_coefficient f hf j, hlc, he]
      exact hcoeff _
    · rw [hf.coeff_eq_zero hm, Int.cast_zero, abs_zero]
      positivity

end
end CCDN
