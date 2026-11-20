/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.Hypersurface.SingularHypersurfaceCount
public import CCDN.Surface.ResidueCover
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Surface.CompleteIntersectionDegreeBudget

/-! A small-curve and residual cover for a surface of controlled
coefficient height. Both the auxiliaries and the initial prime components
are constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

section

variable (f : MvPolynomial (Fin 3) ℤ)
  (hirQ : Irreducible (map (Int.castRingHom ℚ) f))
include f hirQ

/-- The curve components cut out on the surface `f = 0` by the initial auxiliary of a
congruence family: height-two primes containing `f` and the auxiliary, whose zero loci cover
the common zero locus and whose total degree is at most `d A (B^(1/√d) + 1)(1 + log B)`. -/
theorem exists_surface_initial_curve_components {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ I ∈ S, IsSectionCurve (map (Int.castRingHom ℚ) f)
          (map (Int.castRingHom ℚ) F.initial) I (δ I)) ∧
        zeroLocus (map (Int.castRingHom ℚ) f) ∩
          zeroLocus (map (Int.castRingHom ℚ) F.initial) = ⋃ I ∈ S, idealZeroLocus I ∧
        (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * A *
          (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
  obtain ⟨S, δ, hS, hcover, hbudget⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) F.initial) hirQ
      (F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f))
  refine ⟨S, δ, hS, hcover, ?_⟩
  have hinitial : (F.initial.totalDegree : ℝ) ≤
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
    have hh := F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
    simpa only [SurfaceCongruenceFamily.initial, surfaceResidueLogBudget, sum_empty, prod_empty, mul_one, add_zero]
      using hh
  rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
  have hb : (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * F.initial.totalDegree := by
    exact_mod_cast hbudget
  have hm := mul_le_mul_of_nonneg_left hinitial (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  grind

/-- An integral point of the surface `f = 0` is singular, or lies on a component of the initial
cover of degree at most `2 d A Λ(B, W)`, or lies in the residual locus. -/
private theorem surface_point_mem_small_curve_cover
    {A B H : ℝ} {W : Finset ℕ} (hA : 0 ≤ A) (hW : IsSurfaceResidueWindow f B H W)
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3))) (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSectionCurve (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) F.initial) I (δ I))
    (hcover : zeroLocus (map (Int.castRingHom ℚ) f) ∩
      zeroLocus (map (Int.castRingHom ℚ) F.initial) = ⋃ I ∈ S, idealZeroLocus I)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0) :
    rationalPoint x ∈ singularHypersurfaceLocus (map (Int.castRingHom ℚ) f) ∪
      (⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
        2 * f.totalDegree * A * surfaceResidueLogBudget B W), idealZeroLocus I) ∪
      surfaceResidueResidualLocus F S W hW.prime := by
  have hrat {g : MvPolynomial (Fin 3) ℤ} := (eval_rationalPoint_map_eq_zero x g).mpr
  by_cases hsmooth : ∃ j, eval x (pderiv j f) ≠ 0
  · have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
      rw [← hcover]
      exact ⟨hrat hxf, hrat (F.initial_vanishes x hx hxf)⟩
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨I, hIS, hxI⟩ := hxcover
    by_cases hsmall : (δ I : ℝ) ≤ 2 * f.totalDegree * A * surfaceResidueLogBudget B W
    · simp only [Set.mem_union, Set.mem_iUnion, mem_filter]
      exact Or.inl (Or.inr ⟨I, ⟨hIS, hsmall⟩, hxI⟩)
    · right
      exact large_curve_point_mem_surfaceResidueResidualLocus f hirQ hA hW F S I hIS
        (hS I hIS).toIsSurfaceCurve (hS I hIS).mem_right (lt_of_not_ge hsmall) x hx hxf hxI
        hsmooth
  exact Or.inl (Or.inl ⟨hrat hxf, fun j => by
    rw [pderiv_map]
    exact hrat (by aesop)⟩)

end

/-- A small-curve and residual cover of the integral points of the surface `f = 0`: they are
singular, lie on a component of degree at most `2 d A Λ(B, W)` of the curve cover cut out by the
initial auxiliary, or lie in the residual locus. -/
theorem exists_surface_small_curve_residual_cover
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} {W : Finset ℕ} (hK : 0 ≤ K)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) (hW : IsSurfaceResidueWindow f B H W) :
    ∃ F : SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K),
      ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
        ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
          (∀ I ∈ S, IsSectionCurve (map (Int.castRingHom ℚ) f)
            (map (Int.castRingHom ℚ) F.initial) I (δ I)) ∧
          (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) *
            surfaceCongruenceDegreeConstant f.totalDegree K *
            (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) ∧
          count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
            count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B +
            count (⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
              2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
                surfaceResidueLogBudget B W), idealZeroLocus I) B +
            count (surfaceResidueResidualLocus F S W hW.prime) B := by
  classical
  have hA : 0 ≤ surfaceCongruenceDegreeConstant f.totalDegree K :=
    (surfaceCongruenceDegreeConstant_pos f.totalDegree K).le
  have hirQ := rational_irreducible_of_charZero_map f hir
  obtain ⟨F⟩ := exists_surface_congruence_family f hir hd hK hW.one_le_height hW.one_le_radius
    hW.coeff_le hheight
  obtain ⟨S, δ, hS, hcover, hbudget⟩ := exists_surface_initial_curve_components f hirQ F
  refine ⟨F, S, δ, hS, hbudget, ?_⟩
  let singular := singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)
  let retained := ⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
    2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
      surfaceResidueLogBudget B W), idealZeroLocus I
  let residual := surfaceResidueResidualLocus F S W hW.prime
  have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (singular ∪ retained ∪ residual) B := by
    exact count_le_of_integral_mem fun x hx hxf =>
      surface_point_mem_small_curve_cover f hirQ hA hW F S δ hS hcover x hx
        ((eval_rationalPoint_map_eq_zero x f).mp hxf)
  exact hcount.trans ((count_union_le (singular ∪ retained) residual B).trans
    (Nat.add_le_add_right (count_union_le singular retained B) _))

end
end CCDN
