/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Main.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths

@[expose] public section

namespace OAI

noncomputable section

open Real Filter Topology MeasureTheory Polynomial Matrix Set
open scoped TensorProduct RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator Pointwise Topology

namespace EuclideanRamsey

theorem fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by
  have hreal := fieldCriterion_realCriterion a h
  have key : ∀ n : ℕ, 1 ≤ n → ∃ w lmb μ,
      Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ) := by
    intro n hn
    obtain ⟨ℓ,hℓ,f,g,hf,hg,hperm⟩ :=
      realCriterion_two_scale a hd (by omega) hreal (1/(4*n)) (by positivity)
    obtain ⟨w,lmb,μ,hp,hm,hlmb,hμ,hr⟩ :=
      permutation_equal_endpoints a ha f g ((1/(4*n))/(1+1/(4*n))) (1/(4*n*s))
        (by positivity) (by positivity) hf hg hperm
    refine ⟨w,lmb,μ,hp,hm,hlmb,lt_of_le_of_lt hr ?_⟩
    have hs' : (0:ℝ) < s := by positivity
    have h1 : (1/(4*(n:ℝ)))/(1+1/(4*(n:ℝ))) < 1/(4*(n:ℝ)) := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [show (0:ℝ) < 1/(4*(n:ℝ)) by positivity]
    have h2 : (s:ℝ) * (1/(4*(n:ℝ)*(s:ℝ))) = 1/(4*(n:ℝ)) := by field_simp
    have h3 : (1:ℝ)/(4*(n:ℝ)) + 1/(4*(n:ℝ)) < 1/(n:ℝ) := by
      field_simp
      nlinarith
    linarith
  intro r hr
  obtain ⟨D,hD,hmono⟩ := finite_coloring_compactness
    (fun i => FiniteEuclidean.embed d (a i)) r
    (fun c => paths_monochromatic _ key c)
  refine ⟨D,hD,fun c => ?_⟩
  obtain ⟨b,hb,k,hk⟩ := hmono c
  exact ⟨b, fun i j => by rw [dist_eq_norm,dist_eq_norm,hb,← map_sub,LinearIsometry.norm_map], k,hk⟩

end EuclideanRamsey

end

end OAI
