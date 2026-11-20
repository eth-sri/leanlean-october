/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.FieldMapIrreducible
import CCDN.Plane.ProjectivePlaneCount
import CCDN.Analysis.GeometricShells

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Real

/-- On the shell `8^k < 2H ≤ 8^(k+1)`, the plane curve bound supplies
`O(d⁴ 4^k)` points. Their weighted contributions are summable. -/
theorem integer_projective_plane_reciprocal_height_sum : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 3 ≤ d →
    ∀ F : IntegerPolynomial 3, F.IsHomogeneous d → AbsolutelyIrreducible F →
    ∀ s : Finset (ProjectivePoint 2), (∀ x ∈ s, x ∈ projectiveZeroLocus (rationalEquation F)) →
      ∑ x ∈ s, 1/x.mulHeight ≤ C*(d:ℝ)^4 := by
  let C := projectivePlaneAbsoluteConstant
  have hC : 0 < C := projectivePlaneAbsoluteConstant_pos
  refine ⟨16*C,by positivity,?_⟩
  intro d hd F hom hir S hS
  have hd3 : (3:ℝ) ≤ d := by exact_mod_cast hd
  apply (geometric_shell_sum S (fun x => 2*x.mulHeight) _ (r:=8) (M:=8*C*d^4) (by norm_num) (by positivity) (fun x _ => by linarith [x.one_le_mulHeight]) ?_).trans_eq (by ring)
  intro k T hT band
  let B := (8:ℝ)^(k+1)
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hs : T ⊆ projectivePoints (projectiveZeroLocus (rationalEquation F)) B := fun x h => mem_projectivePoints.mpr ⟨by linarith [(band x h).2,x.one_le_mulHeight],hS x (hT h)⟩
  have hc : (T.card:ℝ) ≤ C*d^4*B^(2/(d:ℝ)) := (Nat.cast_le (α:=ℝ)).mpr (card_le_card hs) |>.trans (projective_plane_equation_bound _ (hom.map _) (by omega) (rational_irreducible_of_charZero_map F hir) hB)
  have hp : B^(2/(d:ℝ)) ≤ (4:ℝ)^(k+1) := by
    calc _ ≤ B^(2/3:ℝ) := rpow_le_rpow_of_exponent_le hB (by apply div_le_div_of_nonneg_left <;> linarith)
         _ = _ := by
           dsimp [B]; rw [← rpow_natCast_mul (by norm_num),mul_comm,rpow_mul_natCast (by norm_num)]
           congr 1; rw [show (8:ℝ)=2^(3:ℝ) by norm_num,← rpow_mul (by norm_num)]; norm_num
  calc _ ≤ ∑ _ ∈ T, 2/(8:ℝ)^k := sum_le_sum fun x h => (div_le_div_iff₀ (by linarith [x.one_le_mulHeight]) (by positivity)).mpr (by linarith [(band x h).1])
       _ = (T.card:ℝ)*(2/8^k) := by simp
       _ ≤ (C*d^4*4^(k+1))*(2/8^k) := by gcongr; exact hc.trans (by gcongr)
       _ = _ := by rw [pow_succ,show (1/2:ℝ)=4/8 by norm_num,div_pow]; ring

end
end CCDN
