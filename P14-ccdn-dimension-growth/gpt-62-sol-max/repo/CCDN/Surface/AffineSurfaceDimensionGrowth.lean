/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Surface.AffineSurfaceCountLargeDegree
import CCDN.Surface.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes

/-! The finitely many degrees below the large-degree threshold are absorbed in one constant. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Corrected CCDN Proposition 4.3.4 in every degree at least five: the surface bound
`C d^18 B` for integer equations in three variables with absolutely irreducible top-degree
form. -/
theorem affine_surface_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  obtain ⟨Cbig, hCbig, hbig⟩ := affine_surface_count_large_degree
  classical
  choose C hC hsmall using primitive_surface_fixed_degree_linear_bound
  let S := Finset.range topFormSurfaceThreshold
  have hS : 0 ≤ ∑ d ∈ S, C d := sum_nonneg fun d _ => (hC d).le
  refine ⟨Cbig + ∑ d ∈ S, C d, by positivity, fun f hir hd B hB => ?_⟩
  by_cases hlarge : topFormSurfaceThreshold ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · obtain ⟨u, hprim, hudeg, hutop, ha⟩ := exists_primitive_top_form hir
    have hz : zeroLocus (map (Int.castRingHom ℚ) u) = zeroLocus (map (Int.castRingHom ℚ) f) :=
      Set.ext (rational_model_zero_iff ha)
    rw [← hz]
    have hsum := single_le_sum (f := C) (fun d _ => (hC d).le)
      (mem_range.mpr (lt_of_not_ge hlarge) : f.totalDegree ∈ S)
    have hpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ f.totalDegree by omega))
    exact (hsmall _ u hprim hutop hudeg hd B hB).trans (by
      calc
        _ ≤ (Cbig + ∑ d ∈ S, C d) * 1 * B := by rw [mul_one]; gcongr; linarith
        _ ≤ _ := by gcongr)

end
end CCDN
