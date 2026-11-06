/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousSlice
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.HypersurfaceCoefficientDichotomy
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Plane.UnscaledModelCount

/-! The ordinary homogenization provides an affine auxiliary without a
scaling-prime hypothesis and transfers the coefficient-height dichotomy. -/

public section
namespace CCDN
open MvPolynomial

variable {n : ℕ}

/-- The ordinary homogenization (scaling factor one) of an integer polynomial has the same
coefficient height as the polynomial. -/
lemma integerCoefficientHeight_scaledHomogenize_one  (d : ℕ)
    (f : CCDN.IntegerPolynomial n) :
    integerCoefficientHeight (scaledHomogenize d 1 f) = integerCoefficientHeight f := by
  classical
  have hupper : (integerCoefficientHeight (scaledHomogenize d 1 f) : ℝ) ≤
      integerCoefficientHeight f := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    by_cases hm : ∃ k, homogenizedExponent d k = m
    · obtain ⟨k, rfl⟩ := hm
      simp_all [scaledHomogenize_coefficient, one_pow, one_mul, coefficient_abs_le_integerCoefficientHeight]
    · simp_all [ Finset.sum_eq_zero, coeff_monomial,  Int.cast_zero, abs_zero, scaledHomogenize]
  have hlower := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
      coefficient_abs_le_integerCoefficientHeight (scaledHomogenize d 1 f)
        (homogenizedExponent d m)
  exact_mod_cast le_antisymm hupper hlower


variable {n M : ℕ}

/-- If a form `G` is not divisible by the ordinary homogenization of a nonzero primitive integer
polynomial `f`, then its dehomogenization at `x₀ = 1` is not divisible by `f`. -/
lemma unscaled_auxiliary_not_dvd 
    (f : CCDN.IntegerPolynomial n) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    (G : CCDN.IntegerPolynomial (n + 1)) (hGhom : G.IsHomogeneous M)
    (hGnd : ¬ scaledHomogenize f.totalDegree 1 f ∣ G) :
    ¬ f ∣ homogeneousSlice n 1 G := by
  have hslice : homogeneousSlice n 1 (scaledHomogenize f.totalDegree 1 f) = f := by
    simp only [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hndQ := rational_homogeneousSlice_not_dvd one_ne_zero
    (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hGhom (hprim.scaledHomogenize_one _) (by rw [hslice]) hGnd
  rw [hslice] at hndQ
  exact fun h => hndQ (map_dvd (CCDN.rationalPolynomial) h)

/-- A projective vanishing equation restricts to the integer affine box at any
nonzero homogenizing coordinate whose absolute value is bounded by the radius. -/
lemma scaled_auxiliary_vanishes 
    (f : CCDN.IntegerPolynomial n) (G : CCDN.IntegerPolynomial (n + 1))
    (hGhom : G.IsHomogeneous M) {p : ℤ} (hp : p ≠ 0) {B : ℝ} (hpB : |(p : ℝ)| ≤ B)
    (hGzero : ∀ P : ProjectivePoint n, P.mulHeight ≤ B →
      P ∈ projectiveZeroLocus (CCDN.rationalPolynomial (scaledHomogenize f.totalDegree p f)) →
      P ∈ projectiveZeroLocus (CCDN.rationalPolynomial G)) :
    ∀ x : IntPoint n, InBox x B → eval x f = 0 →
      eval x (homogeneousSlice n p G) = 0 := by
  intro x hx hxf
  let v : IntPoint (n + 1) := Fin.cons p x
  have hv0 : v ≠ 0 := fun h => hp (congrFun h 0)
  let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
  have hvbox : InBox v B := Fin.cases hpB hx
  have hPB : P.mulHeight ≤ B := projective_integer_height_le v hv0 hvbox
  have hvF : eval v (scaledHomogenize f.totalDegree p f) = 0 := by
    rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
  have hPF : P ∈ projectiveZeroLocus
      (CCDN.rationalPolynomial (scaledHomogenize f.totalDegree p f)) := by
    apply (mem_projectiveZeroLocus_mk ((scaledHomogenize_homogeneous p f le_rfl).map _) _ _).mpr
    exact (eval_rationalPoint_eq_zero _ v).mpr hvF
  have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp (hGzero P hPB hPF)
  rw [homogeneousSlice_eval]
  exact (eval_rationalPoint_eq_zero G v).mp hcast

/-- Ordinary homogenization gives an auxiliary in every affine
box, with the height and bad-prime factor of the unscaled model. -/
theorem unscaled_affine_auxiliary 
    (f : CCDN.IntegerPolynomial (n + 2)) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      ↑g.totalDegree ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f))
        (integerCoefficientHeight f : ℝ) := by
  let F := scaledHomogenize f.totalDegree 1 f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  have hFir := (show Irreducible (scaledHomogenize (totalDegree f) (1 : ℤ) f) from (by
                 apply (hprim.scaledHomogenize_one _).irreducible_of_rational_map
                 rw [scaledHomogenize_map]
                 have hdeg : (CCDN.rationalPolynomial f).totalDegree = f.totalDegree :=
                     totalDegree_map_of_injective Int.cast_injective _
                 rw [← hdeg]
                 exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
                   (by simp)))
  obtain ⟨M, hM, G, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd hFir hB
  let g := homogeneousSlice (n + 2) 1 G
  have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hir.ne_zero hprim G hGhom hGnd
  refine ⟨g, ⟨hgnd,
    scaled_auxiliary_vanishes f G hGhom one_ne_zero (by simpa) hGzero⟩, ?_⟩
  have hgM : (g.totalDegree : ℝ) ≤ M := by
    exact_mod_cast homogeneousSlice_degree_le 1 hGhom
  have hh := hgM.trans hM
  simpa only [F, integerCoefficientHeight_scaledHomogenize_one,
    hypersurfaceAuxiliaryDegreeBound, auxDegreeBound, auxMainTerm] using hh

/-- Either the affine equation has controlled coefficient height, or a
degree-at-most-d nonmultiple vanishes on every bounded integer zero. -/
theorem affine_coefficient_height_dichotomy 
    (f : CCDN.IntegerPolynomial n) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((n + f.totalDegree).choose f.totalDegree) +
      ((n + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree * Real.log B ∨
    ∃ g, IsBoxAuxiliary f g B ∧ g.totalDegree ≤ f.totalDegree := by
  rcases projective_coefficient_height_dichotomy (scaledHomogenize f.totalDegree 1 f)
      (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0) hB with
    hheight | ⟨G, hGhom, hGzero, hGnd⟩
  · simp_all [integerCoefficientHeight_scaledHomogenize_one]
  · right
    let g := homogeneousSlice n 1 G
    have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hf0 hprim G hGhom hGnd
    exact ⟨g, ⟨hgnd,
      scaled_auxiliary_vanishes f G hGhom one_ne_zero (by simpa) hGzero⟩, homogeneousSlice_degree_le 1 hGhom⟩

end CCDN
