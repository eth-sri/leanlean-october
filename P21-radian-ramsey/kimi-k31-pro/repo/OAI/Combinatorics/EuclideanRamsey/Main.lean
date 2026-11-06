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


namespace EuclideanRamsey

theorem fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by
  have hreal := fieldCriterion_realCriterion a h
  have hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,
      Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ) := by
    intro n hn
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hs' : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
    let η : ℝ := 1/(4*n)
    let δ : ℝ := 1/(4*n*s)
    have hη : 0<η := by dsimp [η]; positivity
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨ℓ,hℓ,f,g,hf,hg,hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η hη
    have hq : 0<η/(1+η) := div_pos hη (by linarith)
    obtain ⟨w,lmb,μ,hp,hm,hlmb,hμ,hr⟩ :=
      permutation_equal_endpoints a ha f g (η/(1+η)) δ hq hδ hf hg hperm
    refine ⟨w,lmb,μ,hp,hm,hlmb,lt_of_le_of_lt hr ?_⟩
    have hq' : η/(1+η)<η := (div_lt_iff₀ (by linarith : 0<1+η)).mpr (by nlinarith)
    have he : η+(s:ℝ)*δ=1/(2*n) := by
      dsimp [η,δ]
      field_simp
      ring
    have hhalf : (1:ℝ)/(2*n)<1/n := by
      apply one_div_lt_one_div_of_lt hn'
      nlinarith
    rw [← he] at hhalf
    linarith
  intro r hr
  obtain ⟨D,hD,hmono⟩ := finite_coloring_compactness
    (fun i => FiniteEuclidean.embed d (a i)) r
    (fun c => paths_monochromatic _ hpaths c)
  refine ⟨D,hD,?_⟩
  intro c
  obtain ⟨b,hb,k,hk⟩ := hmono c
  refine ⟨b,?_,k,hk⟩
  intro i j
  rw [dist_eq_norm,dist_eq_norm,hb,← map_sub,LinearIsometry.norm_map]

end EuclideanRamsey

end

end OAI
