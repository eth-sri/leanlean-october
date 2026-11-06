/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.SingularHypersurfaceCount
public import CCDN.Surface.ResidueCover
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.CompleteIntersectionDegreeBudget

/-! A small-curve and residual cover for a surface of controlled
coefficient height. Both the auxiliaries and the initial prime components
are constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- A small-curve and residual cover of the integral points of the surface `f = 0`: they are
singular, lie on a component of degree at most `2 d A Λ(B, L)` of the curve cover cut out by the
initial auxiliary, or lie in the residual locus. -/
theorem exists_surface_small_curve_residual_cover
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B L X : ℝ} (hK : 0 ≤ K)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) (hW : IsSurfaceResidueWindow f B H L X) :
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
                surfaceResidueLogBudget B L), idealZeroLocus I) B +
            count (surfaceResidueResidualLocus F S L X hW.one_le_window) B := by
  classical
  let A := surfaceCongruenceDegreeConstant f.totalDegree K
  have hA : 0 ≤ A := (surfaceCongruenceDegreeConstant_pos f.totalDegree K).le
  have hirQ := rational_irreducible_of_charZero_map f hir
  obtain ⟨F⟩ := exists_surface_congruence_family f hir hd hK hW.one_le_height hW.one_le_radius
    hW.coeff_le hheight
  obtain ⟨S, δ, hS, hcover, hbudget, _⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) F.initial) hirQ
      (F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f))
  have hinitial : (F.initial.totalDegree : ℝ) ≤
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
    simpa only [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero]
      using F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
  rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
  have hbudget' : (∑ I ∈ S, (δ I : ℝ)) ≤
      (f.totalDegree : ℝ) * A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) :=
    (show (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * F.initial.totalDegree from
      mod_cast hbudget).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinitial (Nat.cast_nonneg _))
  refine ⟨F, S, δ, hS, hbudget', ?_⟩
  let singular := singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)
  let retained := ⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
    2 * f.totalDegree * A * surfaceResidueLogBudget B L), idealZeroLocus I
  let residual := surfaceResidueResidualLocus F S L X hW.one_le_window
  have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (singular ∪ retained ∪ residual) B := by
    refine card_le_card fun x hx => ?_
    obtain ⟨hbox, hzero⟩ := mem_integralPoints.mp hx
    have hxf : eval x f = 0 := by
      apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
      rw [map_eval, map_zero]; exact hzero
    have hrat {g : MvPolynomial (Fin 3) ℤ} (hg : eval x g = 0) :
        eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
      have hh := congrArg (Int.castRingHom ℚ) hg
      rwa [map_eval, map_zero] at hh
    refine mem_integralPoints.mpr ⟨hbox, ?_⟩
    by_cases hsmooth : ∃ j, eval x (pderiv j f) ≠ 0
    · have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
        rw [← hcover]; exact ⟨hrat hxf, hrat (F.initial_vanishes x hbox hxf)⟩
      obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
      by_cases hsmall : (δ I : ℝ) ≤ 2 * f.totalDegree * A * surfaceResidueLogBudget B L
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr
          ⟨I, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hIS, hsmall⟩, hxI⟩⟩))
      · exact Or.inr (large_curve_point_mem_surfaceResidueResidualLocus f hirQ hA hW F S I hIS
          (hS I hIS).toIsSurfaceCurve (hS I hIS).mem_right (lt_of_not_ge hsmall) x hbox hxf hxI
          hsmooth)
    · refine Or.inl (Or.inl ⟨hrat hxf, fun j => ?_⟩)
      rw [pderiv_map]; exact hrat (not_not.mp fun hn => hsmooth ⟨j, hn⟩)
  exact hcount.trans ((count_union_le (singular ∪ retained) residual B).trans
    (Nat.add_le_add_right (count_union_le singular retained B) _))

end
end CCDN
