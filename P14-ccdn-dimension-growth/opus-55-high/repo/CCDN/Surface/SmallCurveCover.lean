/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.SingularHypersurfaceCount
import CCDN.Surface.ResidueCover
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.CompleteIntersectionDegreeBudget

/-! A small-curve and residual cover for a surface of controlled
coefficient height. Both the auxiliaries and the initial prime components
are constructed. -/

namespace CCDN
open MvPolynomial Finset

variable (f : MvPolynomial (Fin 3) ℤ)

/-- A small-curve and residual cover of the integral points of the surface `f = 0`: they are
singular, lie on a component of degree at most `2 d A Λ(B, L)` of the curve cover cut out by the
initial auxiliary, or lie in the residual locus. -/
theorem exists_surface_small_curve_residual_cover
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
  have hA :=
    (surfaceCongruenceDegreeConstant_pos f.totalDegree K).le
  have hirQ := rational_irreducible_of_charZero_map f hir
  obtain ⟨F⟩ : Nonempty (SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K)) := by
    have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :=
      exists_surface_congruence_auxiliary f hir hd hK hW.one_le_height hW.one_le_radius hW.coeff_le hheight P hP
        (smoothResidueIntegerLift r)
        (fun p hp => by
          let : NeZero p := ⟨(hP p hp).ne_zero⟩
          exact smoothResidueIntegerLift_zero r p hp)
        (fun p hp => by
          let : NeZero p := ⟨(hP p hp).ne_zero⟩
          exact smoothResidueIntegerLift_smooth r p hp)
    choose g hg0 hgproper hgdegree hgzero using hex
    exact ⟨⟨g, hg0, hgproper, hgdegree, hgzero⟩⟩
  obtain ⟨S, δ, hS, hcover, hbudget⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) F.initial) hirQ
      (F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f))
  refine ⟨F, S, δ, hS, ?_, ?_⟩
  · have hinitial : F.initial.totalDegree ≤
        surfaceCongruenceDegreeConstant f.totalDegree K * (B ^ (1 / Real.sqrt f.totalDegree) + 1) * (1 + Real.log B) := by
      have hh := F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
      simpa [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero]
        using hh
    rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
    have hb : (∑ I ∈ S, (δ I : ℝ)) ≤ f.totalDegree * F.initial.totalDegree := by
      exact_mod_cast hbudget
    have hm := mul_le_mul_of_nonneg_left hinitial (Nat.cast_nonneg f.totalDegree)
    exact hb.trans (by grind)
  let singular := singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)
  let retained := ⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
    2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
      surfaceResidueLogBudget B L), idealZeroLocus I
  let residual := surfaceResidueResidualLocus F S L X hW.one_le_window
  have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (singular ∪ retained ∪ residual) B := by
    apply card_le_card
    intro x hx
    obtain ⟨hbox, hzero⟩ := mem_integralPoints.mp hx
    have hxf : eval x f = 0 := by
      apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
      rwa [map_eval, map_zero]
    refine mem_integralPoints.mpr ⟨hbox, ?_⟩
    have hrat {g : MvPolynomial (Fin 3) ℤ} (hg : eval x g = 0) :
        eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
      have hh := congrArg (Int.castRingHom ℚ) hg
      rwa [map_eval, map_zero] at hh
    by_cases hsmooth : ∃ j, eval x (pderiv j f) ≠ 0
    · have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
        rw [← hcover]
        exact ⟨hrat hxf, hrat (show eval x F.initial = 0 from F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x
              (mem_affineCongruencePoints.mpr ⟨hbox, hxf, by simp⟩))⟩
      obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
      by_cases hsmall : (δ I : ℝ) ≤ 2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K * surfaceResidueLogBudget B L
      · aesop
      · right
        obtain ⟨R, hR, p, hp, r, hedge⟩ := surface_residue_boundary_of_large_curve f hirQ hA hW F I
          (hS I hIS).toIsSurfaceCurve (hS I hIS).mem_right (lt_of_not_ge hsmall) x hbox hxf hsmooth
        apply mem_surfaceResidueResidualLocus F S hW.one_le_window R hedge.subset_window hR p hp
          hedge.prod_lt.le r
        classical
        apply Set.mem_iUnion.mpr
        refine ⟨I, Set.mem_iUnion.mpr
          ⟨mem_filter.mpr ⟨hIS, hedge.parent_mem, hedge.child_not_mem⟩, hxI, ?_⟩⟩
        have hh := congrArg (Int.castRingHom ℚ) hedge.child_vanishes
        rwa [map_eval, map_zero] at hh
    · refine Or.inl (Or.inl ?_)
      refine ⟨hrat hxf, fun j => ?_⟩
      rw [pderiv_map]
      grind
  exact hcount.trans ((count_union_le (singular ∪ retained) residual B).trans
    (Nat.add_le_add_right (count_union_le singular retained B) _))

