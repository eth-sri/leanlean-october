/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.AffineSurfaceCountLargeDegree
import CCDN.Surface.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes

/-!
The affine surface bound in every degree at least five. The finitely many
degrees below the large-degree threshold are absorbed in one constant.

Removing integer content from the fixed-degree surface estimate.
The resulting constant is uniform in all integer coefficients.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

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
  /- The fixed-degree surface bounds for the degrees `5 ≤ d < t` hold with one constant. -/
  have hsmall_ex (t : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f → 5 ≤ f.totalDegree → f.totalDegree < t →
      ∀ B : ℝ, 1 ≤ B → (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
    induction t with
    | zero => exact ⟨1, one_pos, fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
    | succ t ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      by_cases ht : 5 ≤ t
      · obtain ⟨C', hC', hbound'⟩ := primitive_surface_fixed_degree_linear_bound t ht
        refine ⟨C + C', by positivity, fun f hir hd hlt B hB => ?_⟩
        have hB0 : 0 ≤ B := by linarith
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
        · exact (hbound f hir hd hlt B hB).trans (by gcongr; linarith)
        · have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by simp [hz])
          obtain ⟨c, u, hc, hprim, he⟩ := exists_primitive_integer_factor f hf0
          obtain ⟨hudeg, hutop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
          rw [show zeroLocus (map (Int.castRingHom ℚ) f) = zeroLocus (map (Int.castRingHom ℚ) u) by
            ext x
            change eval x (map (Int.castRingHom ℚ) f) = 0 ↔ eval x (map (Int.castRingHom ℚ) u) = 0
            rw [he, map_mul, map_C, eval_mul, eval_C]
            exact mul_eq_zero_iff_left (show (c : ℚ) ≠ 0 from mod_cast hc)]
          exact (hbound' u hprim hutop (hudeg.trans heq) B hB).trans (by gcongr; linarith)
      · exact ⟨C, hC, fun f hir hd hlt => hbound f hir hd (by omega)⟩
  obtain ⟨Cbig, hCbig, hbig⟩ := affine_surface_count_large_degree
  obtain ⟨Csmall, hCsmall, hsmall⟩ := hsmall_ex topFormSurfaceThreshold
  refine ⟨Cbig + Csmall, by positivity, fun f hir hd B hB => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
    one_le_pow₀ (mod_cast (show 1 ≤ f.totalDegree by omega))
  by_cases hlarge : topFormSurfaceThreshold ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · exact (hsmall f hir hd (by omega) B hB).trans
      ((by gcongr; linarith : _ ≤ (Cbig + Csmall) * 1 * B).trans (by gcongr))

end
end CCDN
