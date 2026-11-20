/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.ClassGroup.PrimitiveGeneratorCount
import CCDN.ClassGroup.TranslateFibers

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped IntermediateField
universe u

/-- The CCDN two-torsion bound, with one logarithm in even degree and none in odd degree. -/
theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (classGroupTwoTorsionCard K : ℝ) ≤
          C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(discr K : ℝ)|) ^ (1 - n % 2) := by
  classical
  obtain ⟨C,hC,hsub⟩ := imprimitive_class_bound.{u,u} n hn
  have hcost : 0 ≤ primitiveClassCost n := by
    have := (affineHypersurfaceAuxiliaryConstant_pos 0).le
    have := numberFieldLatticeBoxConstant_nonneg n (sq_nonneg (n:ℝ))
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9)
    dsimp only [primitiveClassCost,curveFiberCost]; positivity
  refine ⟨primitiveClassCost n+C,by positivity,?_⟩
  intro K _ _ hdeg
  obtain ⟨β,hi,hβ⟩ := exists_injective_balanced_two_torsion_generators K
  choose J hclass hsq hnorm using fun c => (hβ c).2.2
  let L := fun c => ℚ⟮(-(β c : K))⟯
  let p := fun c => L c = ⊤
  have hf := primitive_class_bound K (by dsimp [fieldDegree]; omega) (fun i : Subtype p => β i.val)
    (hi.comp Subtype.val_injective) (fun i => ⟨(hβ i.val).1,fun w => ((hβ i.val).2.1 w).le,_,hnorm i.val⟩) (fun i => i.property)
  have he := hsub K hdeg (fun i : {i // ¬ p i} => J i.val) (fun i => β i.val) (fun i j h => by
      exact Subtype.ext (Subtype.ext (by simpa only [Function.comp_apply,hclass] using h)))
    (fun i => (hβ i.val).1) (fun i => hsq i.val) (fun i => ⟨L i.val,i.property,by
      simpa using (L i.val).neg_mem (IntermediateField.mem_adjoin_simple_self ℚ (-(β i.val : K)))⟩)
  let D := absDiscriminant K
  have hlog := one_le_log_abs_discr K (by omega)
  have hW : 1 ≤ parityWeight n (Real.log D) := by unfold parityWeight; split <;> first | exact le_rfl | exact hlog
  have hWeq : (Real.log D)^(1-n%2) = parityWeight n (Real.log D) := by
    by_cases ho : Odd n
    · simp [parityWeight,ho,Nat.odd_iff.mp ho]
    · simp [parityWeight,ho,Nat.not_odd_iff.mp ho]
  change _ ≤ _ * D^classExponent n * (Real.log D)^(1-n%2)
  rw [hWeq,classGroupTwoTorsionCard,← Nat.card_congr (Equiv.sumCompl p),Nat.card_sum,Nat.cast_add]
  dsimp only [fieldDegree] at hf; rw [hdeg] at hf
  apply (add_le_add hf (he.trans (le_mul_of_one_le_right (by positivity) hW))).trans_eq
  ring

end
end CCDN
