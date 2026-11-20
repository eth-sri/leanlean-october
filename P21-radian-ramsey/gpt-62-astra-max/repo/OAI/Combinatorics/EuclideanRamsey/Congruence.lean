/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module
public import OAI.Combinatorics.EuclideanRamsey.Model
@[expose] public section
namespace OAI.EuclideanRamsey
open scoped RealInnerProductSpace

def AffineRow {d} (a : Fin 9 → Space d) (b : Fin 9 → ℝ) := ∃ v x, ∀ i, b i = v+⟪a i,x⟫

/-- Each coordinate of a congruent copy is an affine function of the original
point. Project the coordinate vector onto the span of the differences; their
Gram matrix, and hence each such inner product, transfers to the original. -/
theorem column {D d} {a : Fin 9 → Space d} {b : Fin 9 → Space D} (h : Congruent a b) (j : Fin D) :
    AffineRow a (fun i => b i j) := by
  let B := Fintype.linearCombination ℝ fun i => b i-b 0
  let A := Fintype.linearCombination ℝ fun i => a i-a 0
  obtain ⟨_,⟨c,rfl⟩,e,he,eq⟩ := B.range.exists_add_mem_mem_orthogonal (EuclideanSpace.single j 1)
  have gram (i k) : ⟪b i-b 0,b k-b 0⟫ = ⟪a i-a 0,a k-a 0⟫ := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,sub_sub_sub_cancel_right,← dist_eq_norm,h i 0,h k 0,h i k]
  refine ⟨b 0 j-⟪a 0,A c⟫,A c,fun i => ?_⟩
  have h' : ⟪b i-b 0,EuclideanSpace.single j 1⟫ = ⟪a i-a 0,A c⟫ := by
    have mem : b i-b 0 ∈ B.range := ⟨Pi.single i 1,by simp [B]⟩
    simp [eq,Submodule.inner_right_of_mem_orthogonal mem he,A,B,Fintype.linearCombination_apply,inner_add_right,inner_sum,inner_smul_right,gram]
  simp [inner_sub_left,EuclideanSpace.inner_single_right] at h'
  linarith

end OAI.EuclideanRamsey
