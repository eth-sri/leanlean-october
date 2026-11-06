/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

public section

namespace OAI.EuclideanRamsey



open scoped RealInnerProductSpace

theorem congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
  classical
  have hs : Submodule.span ℝ (Set.range fun i => a i-a i₀) = ⊤ := by
    simpa [direction_affineSpan,vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] using
      congrArg AffineSubspace.direction hspan
  have hg i j : ⟪b i - b i₀, b j - b i₀⟫ =
      ⟪a i - a i₀, a j - a i₀⟫ := by
    simp [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← dist_eq_norm]
    rw [h i i₀, h j i₀, h i j]
  let x := fun i => a i-a i₀
  let y := fun i => b i-b i₀
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hnorm c : ‖B c‖ = ‖A c‖ := by
    rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner]
    congr 1
    simp only [A,B,Fintype.linearCombination_apply,sum_inner,inner_sum,
      real_inner_smul_left,inner_smul_right,x,y,hg]
  have hsurj : Function.Surjective A := LinearMap.range_eq_top.mp (by aesop)
  let Q := B.extendOfIsometry hsurj.denseRange hnorm
  have hQ (i) : Q (a i-a i₀) = b i-b i₀ := by
    simpa [A,B,x,y,Q] using B.extendOfIsometry_eq hsurj.denseRange hnorm (Pi.single i 1)
  refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
  grind

end OAI.EuclideanRamsey
