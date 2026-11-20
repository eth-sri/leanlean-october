/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.TopFormSurfaceComponents
import CCDN.Surface.AuxiliaryExponent

/-! The corrected large-degree surface bound. The auxiliary section's
nonlinear curves and its degree-one components together account
for every bounded integer zero of the original surface. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The degree threshold of the large-degree surface bound `affine_surface_count_large_degree`. It
comes from `surface_inverse_sqrt_le_quarter`: `1 / √d ≤ 1 / 4` once `16 ≤ d`. -/
def topFormSurfaceThreshold : ℕ := 16

/-- Corrected CCDN Proposition 4.3.4 for degrees at least sixteen and an
absolutely irreducible highest homogeneous part. The positive constant is
chosen before the integer polynomial and the real box radius. -/
theorem affine_surface_count_large_degree :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      topFormSurfaceThreshold ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  classical
  obtain ⟨C, K, hC, hK, hcount⟩ := surface_curve_union_bound
  let A := topFormAuxiliaryConstant 1
  have hA := topFormAuxiliaryConstant_pos 1
  let M := K * Real.exp 1 * (480 * A + 2 * A ^ 4)
  refine ⟨C + M + A, by positivity, ?_⟩
  intro f hir hd B hB
  change 16 ≤ f.totalDegree at hd
  obtain ⟨S, δ, hS, hsum, hcover⟩ := top_form_surface_curve_components f hir hB
  let T := S.filter (fun P => 2 ≤ δ P)
  let D := (f.totalDegree : ℝ) ^ 18 * B
  have hlarge := sum_curveBound_le_surface_degree_budget T δ hd hA.le hB
    (fun _ hP => (Finset.mem_filter.mp hP).2)
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)).trans hsum)
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast (show 1 ≤ f.totalDegree by omega)
  have hd18 : (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) ≤ (f.totalDegree : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (9 / 2 : ℝ) ≤ 18)
  have hB1 : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ B := by
    exact (Real.rpow_le_rpow_of_exponent_le hB
      (show 1 / Real.sqrt (f.totalDegree : ℝ) ≤ 1 from
        (div_le_one (by positivity)).mpr (Real.one_le_sqrt.mpr hd1))).trans_eq (Real.rpow_one _)
  have hbudget : (∑ P ∈ S, (δ P : ℝ)) ≤ A * D := by
    refine hsum.trans ?_
    dsimp only [D]
    rw [mul_assoc]
    gcongr
  have hd6 := pow_le_pow_right₀ hd1 (show 6 ≤ 18 by decide)
  calc
    _ ≤ (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_le_of_integral_mem (fun x hx hf => by
        simpa only [Set.mem_iUnion, exists_prop] using hcover x hx ((eval_rationalPoint_map_eq_zero x f).mp hf))
    _ ≤ _ := hcount f hir (by omega) S δ B hB hS
    _ ≤ C * (f.totalDegree : ℝ) ^ 18 * B +
          K * (Real.exp 1 * (480 * A + 2 * A ^ 4) * (f.totalDegree : ℝ) ^ 18 * B) + A * D := by
      gcongr
    _ = _ := by dsimp only [D, M]; ring

end
end CCDN
