/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Surface.CurveComponents
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.SmallDegreeSurfaceCurveCount

/-! The retained part of the small-degree surface cover. Lines and
nonlinear prime curves are counted together, using their common degree
budget and the logarithmic cap on the retained degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- There is an absolute constant `C` such that, for an integer surface equation `f` of degree
`d ≥ 5` with absolutely irreducible top-degree form and a finite family `S` of curves of
positive degree on the surface, each of degree at most `D (log B + 1)` and of total degree at
most `A B^(1/√d) (log B + 1)`, the union of the curves has at most
`C (d⁶ + A (D² (D + 1) + 1)) B` integral points of height at most `B`. -/
theorem retained_surface_curve_union_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (A D B : ℝ),
      0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I)) →
      (∀ I ∈ S, (δ I : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ I ∈ S, (δ I : ℝ)) ≤
        A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) →
      (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
        C * ((f.totalDegree : ℝ) ^ 6 + A * (D ^ 2 * (D + 1) + 1)) * B := by
  obtain ⟨Cline, K, hCline, hK, hcount⟩ := surface_curve_union_bound
  let D₀ := logarithmicBoxConstant 4 (1 / 20)
  let D₁ := logarithmicBoxConstant 1 (1 / 20)
  let C := Cline + K * D₀ + D₁
  have hD₀ : 0 ≤ D₀ := by positivity
  have hD₁ : 0 ≤ D₁ := by positivity
  refine ⟨C, by positivity, ?_⟩
  intro f hir hd S δ A D B hA hD hB hS hcap hbudget
  let T := S.filter (fun P => 2 ≤ δ P)
  have hsmall := sum_curveBound_logarithmic_degrees T δ hd hA hD hB
    (fun _ hP => (mem_filter.mp hP).2) (fun P hP => hcap P (mem_filter.mp hP).1)
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget)
  have hweight : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ≤ D₁ * B := by
    simpa only [pow_one] using box_polylog_weight 1 (by norm_num : (0 : ℝ) < 1 / 20) hB
      (t := 1 / Real.sqrt (f.totalDegree : ℝ)) (by linarith [surface_inverse_sqrt_le_nine_twentieths hd])
  have hbudget' : (∑ I ∈ S, (δ I : ℝ)) ≤ A * (D₁ * B) := by
    exact hbudget.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hweight hA)
  calc
    _ ≤ _ := hcount f hir (by omega) S δ B hB hS
    _ ≤ Cline * (f.totalDegree : ℝ) ^ 6 * B + K * (D₀ * A * D ^ 2 * (D + 1) * B) + A * (D₁ * B) := by
      gcongr
    _ ≤ _ := by
      dsimp only [C]
      nlinarith only [mul_nonneg (show 0 ≤ K * D₀ + D₁ by positivity)
          (show 0 ≤ (f.totalDegree : ℝ) ^ 6 * B by positivity),
        mul_nonneg (show 0 ≤ Cline + D₁ by positivity) (show 0 ≤ A * D ^ 2 * (D + 1) * B by positivity),
        mul_nonneg (show 0 ≤ Cline + K * D₀ by positivity) (show 0 ≤ A * B by positivity)]

end
end CCDN
