/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.Algebra.HomogeneousSlice
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.Determinant.HomogeneousDeterminantComparison
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Algebra.ScaledHomogenizationPrimitive

/-! Transfer auxiliary polynomials from scaled homogeneous models to an affine box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The ordinary homogenization (scaling factor one) of an integer polynomial has the same
coefficient height as the polynomial. -/
lemma integerCoefficientHeight_scaledHomogenize_one {n : ℕ} (d : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integerCoefficientHeight (scaledHomogenize d 1 f) = integerCoefficientHeight f := by
  classical
  have hupper : (integerCoefficientHeight (scaledHomogenize d 1 f) : ℝ) ≤
      integerCoefficientHeight f := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    by_cases hm : ∃ k, homogenizedExponent d k = m
    · obtain ⟨k, rfl⟩ := hm
      simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
        coefficient_abs_le_integerCoefficientHeight f k
    simp_all [scaledHomogenize]
  have hlower : (integerCoefficientHeight f : ℝ) ≤
      integerCoefficientHeight (scaledHomogenize d 1 f) := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
      coefficient_abs_le_integerCoefficientHeight (scaledHomogenize d 1 f)
        (homogenizedExponent d m)
  exact_mod_cast le_antisymm hupper hlower

private lemma scaled_auxiliary_not_dvd {n M : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {a : ℤ} (ha : a ≠ 0)
    (hprim : PrimitiveIntegerPolynomial (scaledHomogenize f.totalDegree a f))
    (G : MvPolynomial (Fin (n + 1)) ℤ) (hGhom : G.IsHomogeneous M)
    (hGnd : ¬ scaledHomogenize f.totalDegree a f ∣ G) : ¬ f ∣ homogeneousSlice n a G := by
  have hslice := homogeneousSlice_scaledHomogenize a f le_rfl
  have hdeg : (homogeneousSlice n a (scaledHomogenize f.totalDegree a f)).totalDegree = f.totalDegree := by
    rw [hslice, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ ha)) hf,
      totalDegree_C, zero_add]
  intro hg
  apply rational_homogeneousSlice_not_dvd ha (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ ha hf) hGhom hprim hdeg hGnd
  rw [hslice, map_mul, map_C, map_pow]
  exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Int.cast_ne_zero.mpr ha : (a : ℚ) ≠ 0))).map C)
    |>.mul_left_dvd.mpr (map_dvd (map (Int.castRingHom ℚ)) hg)

/-- The affine auxiliary from a primitive scaled homogeneous model. The same argument
covers ordinary homogenization and the prime scalings used for large boxes. -/
theorem scaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {a : ℤ} (ha : a ≠ 0) (hprim : PrimitiveIntegerPolynomial (scaledHomogenize f.totalDegree a f))
    {B : ℝ} (hB : 1 ≤ B) (haB : |(a : ℝ)| ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree a f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree a f) : ℝ) := by
  let F := scaledHomogenize f.totalDegree a f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd (scaledHomogenize_integer_irreducible f hir hd ha hprim) hB
  have hnd := scaled_auxiliary_not_dvd f hir.ne_zero ha hprim G hGhom hGnd
  refine ⟨homogeneousSlice (n + 2) a G, ⟨?_, hnd, ?_⟩, ?_⟩
  · exact fun h => hnd (h ▸ dvd_zero f)
  · intro x hx hxf
    let v : IntPoint (n + 3) := Fin.cons a x
    have hv0 : v ≠ 0 := fun h => ha (congrFun h 0)
    have hvbox : InBox v B := fun j => Fin.cases haB hx j
    let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
    have hvF : eval v F = 0 := by rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
    have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp
      (hGzero P (projective_integer_height_le v hv0 hvbox) ((mem_projectiveZeroLocus_mk (hFhom.map _) _ _).mpr ((eval_rationalPoint_map_eq_zero v F).mpr hvF)))
    rw [homogeneousSlice_eval]
    exact (eval_rationalPoint_map_eq_zero v G).mp hcast
  · exact (Nat.cast_le.mpr (homogeneousSlice_degree_le a hGhom)).trans hM

/-- A large coefficient height forces a degree-at-most-d auxiliary. Apply the determinant
height bound to the actual affine points, written with first coordinate one. -/
theorem affine_coefficient_height_dichotomy {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((n + f.totalDegree).choose f.totalDegree) +
      ((n + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree * Real.log B ∨
    ∃ g, IsBoxAuxiliary f g B ∧ g.totalDegree ≤ f.totalDegree := by
  classical
  let S := (integerBox n B).filter (fun x => eval x f = 0)
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 1) := fun i => Fin.cons 1 (e i).val
  let F := scaledHomogenize f.totalDegree 1 f
  have hF := scaledHomogenize_homogeneous 1 f le_rfl
  have hF0 := scaledHomogenize_ne_zero f.totalDegree one_ne_zero hf
  by_cases hrel : ∀ G : MvPolynomial (Fin (n + 1)) ℤ, G.IsHomogeneous f.totalDegree →
      (∀ i, eval (z i) G = 0) → F ∣ G
  · left
    rw [← integerCoefficientHeight_scaledHomogenize_one f.totalDegree f]
    refine homogeneous_no_auxiliary_coefficient_height F hF hF0 z ?_ hB ?_ hrel
    · intro i
      rw [scaledHomogenize_eval _ _ le_rfl, (Finset.mem_filter.mp (e i).property).2, mul_zero]
    · intro i j
      exact Fin.cases (by simpa [z] using hB) (mem_integerBox.mp (Finset.mem_filter.mp (e i).property).1) j
  · push Not at hrel
    obtain ⟨G, hGhom, hGzero, hGnd⟩ := hrel
    right
    have hnd := scaled_auxiliary_not_dvd f hf one_ne_zero (hprim.scaledHomogenize_one _) G hGhom hGnd
    refine ⟨homogeneousSlice n 1 G, ⟨fun h => hnd (h ▸ dvd_zero f), hnd, ?_⟩,
      homogeneousSlice_degree_le 1 hGhom⟩
    intro x hx hxf
    obtain ⟨i, hi⟩ := e.surjective ⟨x, Finset.mem_filter.mpr ⟨mem_integerBox.mpr hx, hxf⟩⟩
    rw [homogeneousSlice_eval]
    simpa only [z, hi] using hGzero i

end
end CCDN
