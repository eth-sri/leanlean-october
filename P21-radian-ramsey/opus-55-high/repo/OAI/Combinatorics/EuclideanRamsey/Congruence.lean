/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

public section

open scoped RealInnerProductSpace

set_option autoImplicit true
namespace OAI.EuclideanRamsey

theorem linearIsometry_of_equal_gram [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    x (y : ι → F)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (hgram : ∀ i j, ⟪y i, y j⟫ = ⟪x i, x j⟫) :
    ∃ Q : E →ₗᵢ[ℝ] F, ∀ i, Q (x i) = y i := by
  classical
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hnorm c : ‖B c‖ = ‖A c‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, hgram]
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective (by aesop)
  have hR' z : A (R z) = z := LinearMap.congr_fun hR z
  have hf c : B (R (A c)) = B c := by
    rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hnorm]
    simp [hR']
  exact ⟨⟨B.comp R, fun z => by simp_all⟩, fun i => by simpa [A, B] using hf (Pi.single i 1)⟩

theorem congruent_linearIsometry a
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t, ∀ i, b i = t + Q (a i) := by
  have hv := congrArg AffineSubspace.direction hspan
  rw [direction_affineSpan, AffineSubspace.direction_top,
    vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
  obtain ⟨Q, hQ⟩ := linearIsometry_of_equal_gram _ (fun i => b i - b i₀) hv fun i j => by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, vsub_eq_sub, h i i₀, h j i₀, h i j]
  simp at hQ
  exact ⟨Q, b i₀ - Q (a i₀), fun i => by grind⟩
