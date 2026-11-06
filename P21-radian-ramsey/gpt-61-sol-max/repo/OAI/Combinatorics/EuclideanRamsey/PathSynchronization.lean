/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section




variable {ι : Type*} {a : ι → FiniteEuclidean}

def scaleGroup (c : ℝ) : LetterGroup →* LetterGroup := FreeGroup.map (fun z => Real.sqrt c • z)
lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | @copy u b hb =>
    have hcopy : CopyPath a (c*u) (fun i => Real.sqrt c • b i) := by
      refine ⟨mul_nonneg hc hb.1,?_⟩
      intro i j
      rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc,hb.2]
      ring
    simpa [scaleGroup] using Path.copy _ hcopy
  | mul _ _ ihu ihv => simpa [Pi.mul_def, mul_add] using ihu.mul ihv

theorem synchronize_paths (n : ℕ) (hn : 1 ≤ n) {w : ι → LetterGroup} {lmb μ : ℝ}
    (hp : Path a w lmb) (hm : Path a w μ) (hlmb : 0 < lmb)
    (hratio : μ/lmb < 1/(n:ℝ)) :
    ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path a W (1/(t:ℝ)) := by
  let ρ := μ/lmb
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hρ : ρ<1 := lt_of_lt_of_le hratio ((div_le_one hn').mpr (by exact_mod_cast hn))
  have hnorm : Path a (fun i => scaleGroup lmb⁻¹ (w i)) 1 := by
    simpa [inv_mul_cancel₀ hlmb.ne'] using hp.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  have hnorm' : Path a (fun i => scaleGroup lmb⁻¹ (w i)) ρ := by
    simpa [ρ,div_eq_mul_inv,mul_comm] using hm.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  let v j : ℝ := if j<n then 1/(j+1:ℕ) else ρ
  have hv0 : v 0=1 := by simp [v]; omega
  have hvn : v n=ρ := by simp [v]
  have hv j (hj : j<n) : v (j+1)≤v j := by
    dsimp [v]
    rw [ite_eq_left hj]
    split_ifs with hj'
    · apply one_div_le_one_div_of_le (by positivity)
      simp
    · have he : j+1=n := by omega
      simpa [he,ρ] using hratio.le
  let w' := fun i => scaleGroup lmb⁻¹ (w i)
  let c j := (v j-v (j+1))/(1-ρ)
  have hc : ∀ j,j<n → 0 ≤ c j := fun j hj => div_nonneg (sub_nonneg.mpr (hv j hj)) (by linarith)
  let ww j : ι → LetterGroup := fun i => scaleGroup (c j) (w' i)
  refine ⟨((List.range n).map ww).prod,?_⟩
  intro t ht htn
  let k := t-1
  have hk : k≤n := by dsimp [k]; omega
  let u j := if j<k then c j*ρ else c j
  have hpaths : ∀ j∈List.range n,Path a (ww j) (u j) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    dsimp [u]
    split_ifs
    · exact hnorm'.scale (c j) (hc j hj')
    · simpa using hnorm.scale (c j) (hc j hj')
  have hs : ∑ j∈Finset.range n,u j=v k := by
    rw [← Finset.sum_range_add_sum_Ico u hk]
    dsimp only [u]
    rw [Finset.sum_ite_of_true (fun j hj => Finset.mem_range.mp hj),
      Finset.sum_ite_of_false (fun j hj => not_lt.mpr (Finset.mem_Ico.mp hj).1),
      ← Finset.sum_mul,Finset.sum_Ico_eq_sub _ hk]
    simp only [c, ← Finset.sum_div, Finset.sum_range_sub', hv0, hvn]
    field_simp [ne_of_gt (show 0 < 1-ρ by linarith)]
    ring
  have hvk : v k=1/(t:ℝ) := by
    simp only [v, k, ite_eq_left (show t-1<n by omega), Nat.sub_add_cancel ht]
  rw [← hvk, ← hs]
  change Path a ((List.range n).map ww).prod ((List.range n).map u).sum
  generalize List.range n = l at hpaths ⊢
  induction l with
  | nil => simpa [Pi.one_def] using (Path.diag (a:=a) 1)
  | cons j l ih =>
    simpa using (hpaths j (by simp)).mul (ih (fun k hk => hpaths k (by simp [hk])))
end

end OAI.EuclideanRamsey
