/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.WindowCover
import CCDN.Algebra.FieldMapIrreducible
import CCDN.Hypersurface.SingularHypersurfaceCount
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.CoefficientReduction
import CCDN.Surface.CurveCoverCost
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.Surface.TopFormBadPrimes
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset SurfaceWindow

/-- For each degree `d ≥ 5`, there is a constant `C` such that every primitive integer
surface equation of degree `d` with absolutely irreducible top-degree form has at most `C B`
integral points of height at most `B` on its zero set, for every `B ≥ 1`. -/
theorem primitive_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : IntegerPolynomial 3, PrimitiveIntegerPolynomial f → HasAbsIrreducibleTopForm f →
    f.totalDegree = d → ∀ B : ℝ, 1 ≤ B → (count (zeroLocus (rationalEquation f)) B : ℝ) ≤ C*B := by
  classical
  let K := surfaceCoefficientLogConstant d
  have hK := (surfaceCoefficientLogConstant_pos d).le
  let A := surfaceCongruenceDegreeConstant d K
  have hA : 0 ≤ A := (surfaceCongruenceDegreeConstant_pos d K).le
  let N := surfaceWindowSize d K
  let D := d * levelCost N A
  have hD : 0 ≤ D := by dsimp only [D,levelCost]; positivity
  let E := 2*(d:ℝ)*A
  have hE : 0 ≤ E := by positivity
  obtain ⟨C,hC,curves⟩ := surface_curve_cover_cost
  obtain ⟨c,hc,weight⟩ := surface_window_weight
  let ret := C*((d:ℝ)^6+E*(1+D^3)*logWeight)
  let res := residualCost N d A
  have hw : 0 ≤ logWeight := by unfold logWeight; positivity
  have hret : 0 ≤ ret := by positivity
  have hres : 0 ≤ res := by unfold res residualCost residueCost; positivity
  refine ⟨9*(d:ℝ)^2+ret+res*c+1,by positivity,?_⟩
  intro f prim top he B hB
  subst d
  let q := rationalEquation f
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f top
  have hir := rational_irreducible_of_charZero_map f habs
  have hlog := Real.log_nonneg hB
  rcases primitive_surface_coefficient_reduction f prim hir hB with height | many
  · have hH : (1:ℝ) ≤ integerCoefficientHeight f := by exact_mod_cast integerCoefficientHeight_pos f (ne_zero_of_irreducible_map habs)
    obtain ⟨W⟩ := exists_surfaceWindow hB N
    obtain ⟨F⟩ := exists_surface_congruence_family f prim habs (by omega) hK hH hB (coefficient_abs_le_integerCoefficientHeight f) height
    obtain ⟨S,δ,hS,cover,budget⟩ := exists_surface_initial_curve_components f hir F
    let small := S.filter (fun I => (δ I:ℝ) ≤ D*boxLog B)
    let X := ⋃ I ∈ small, idealZeroLocus I
    let Y := singularHypersurfaceLocus q
    let Z := W.residual F S
    have hr : 1 ≤ B^(1/Real.sqrt (f.totalDegree:ℝ)) := Real.one_le_rpow hB (by positivity)
    have hsmall : (count X B:ℝ) ≤ ret*B := by
      have hc := curves f top (by omega) small δ (D*boxLog B) (E*B^(1/Real.sqrt (f.totalDegree:ℝ))*boxLog B) B hB (by dsimp only [boxLog]; positivity)
        (by intro I h; have hh := hS I (mem_filter.mp h).1; exact ⟨hh.toIsSurfaceCurve,hh.pos⟩)
        (fun _ h => (mem_filter.mp h).2)
        (by
          apply (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.cast_nonneg (α:=ℝ) _)).trans (budget.trans ?_)
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show B^(1/Real.sqrt (f.totalDegree:ℝ))+1 ≤ 2*B^(1/Real.sqrt (f.totalDegree:ℝ)) by linarith) (show 0 ≤ (f.totalDegree:ℝ)*A by positivity)) (show 0 ≤ 1+Real.log B by linarith)
          dsimp only [E,boxLog]; linarith)
      have hcost := retained_curve_cost hd hE hD hB
      calc
        _ ≤ _ := hc
        _ ≤ C*((f.totalDegree:ℝ)^6*B+E*(1+D^3)*logWeight*B) := by gcongr
        _ = _ := by dsimp [ret]; ring
    have hsing : (count Y B:ℝ) ≤ 9*(f.totalDegree:ℝ)^2*B := by
      convert singular_hypersurface_dimension_growth (n:=1) q hir hB using 1; norm_num [q,rational_map_totalDegree]
    have hz : (count Z B:ℝ) ≤ res*(c*B) := (W.residual_bound F S δ (fun I h => (hS I h).toIsSurfaceCurve) hir hd hB hA).trans (mul_le_mul_of_nonneg_left (weight B hB) hres)
    have hcov : count (zeroLocus q) B ≤ count Y B + count X B + count Z B := by
      refine (count_le_of_box_imp (Y := Y ∪ X ∪ Z) ?_).trans ((count_union_le _ _ _).trans (Nat.add_le_add_right (count_union_le _ _ _) _))
      intro x hx hf
      have hxf : eval x f = 0 := mem_integer_zeroLocus.mp hf
      by_cases hs : ∃ j, eval x (pderiv j f) ≠ 0
      · have hxs : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := cover x hx hxf
        simp only [Set.mem_iUnion] at hxs
        obtain ⟨I,hi,hxI⟩ := hxs
        by_cases h : (δ I:ℝ) ≤ D*boxLog B
        · exact Or.inl (Or.inr (by simpa [X,Set.mem_iUnion] using ⟨I,mem_filter.mpr ⟨hi,h⟩,hxI⟩))
        · obtain ⟨P,hP,hk,hs⟩ := W.smooth_subset hB hH (coefficient_abs_le_integerCoefficientHeight f) height x hx hs
          exact Or.inr (W.large_curve_mem_residual F S hB hA hd hir hi (hS I hi).toIsSurfaceCurve (hS I hi).mem_right (lt_of_not_ge h) x hx hxf hxI P hP hk hs)
      · push Not at hs
        exact Or.inl (Or.inl ⟨hf,fun j => by change eval _ (pderiv _ (rationalEquation f)) = 0; rw [pderiv_map,eval_rationalPoint_map,hs,Int.cast_zero]⟩)
    have hh := (Nat.cast_le (α:=ℝ)).mpr hcov
    push_cast at hh
    change (count (zeroLocus q) B:ℝ) ≤ _
    linarith
  · nlinarith [sq_nonneg (f.totalDegree:ℝ),mul_nonneg hret (zero_le_one.trans hB),mul_nonneg (mul_nonneg hres hc.le) (zero_le_one.trans hB)]

end
end CCDN
