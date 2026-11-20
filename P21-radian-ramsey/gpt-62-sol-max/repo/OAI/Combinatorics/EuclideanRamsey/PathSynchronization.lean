/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathWords

@[expose] public section

namespace OAI.EuclideanRamsey

universe uIndex uAlpha

noncomputable section

open Finset

variable {ι : Type uIndex} {a : ι → Hilbert}

def scaleGroup (c : ℝ) : LetterGroup →* LetterGroup := FreeGroup.map (fun z => Real.sqrt c • z)
lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | @copy u b hb =>
    refine Path.copy _ ⟨mul_nonneg hc hb.1,fun i j => ?_⟩
    rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc,hb.2]
    ring
  | mul _ _ ihu ihv => simpa only [map_mul,Pi.mul_apply,Pi.mul_def,mul_add] using ihu.mul ihv

lemma Path.list_prod {α : Type uAlpha} (l : List α) (w : α → ι → LetterGroup) (u : α → ℝ)
    (h : ∀ j∈l,Path a (w j) (u j)) :
    Path a (fun i => (l.map (fun j => w j i)).prod) ((l.map u).sum) := by
  induction l with
  | nil => tauto
  | cons j l ih =>
    simpa [Pi.mul_def] using (h j (by simp)).mul (ih (fun k hk => h k (by simp [hk])))

/-- Finitely many conditions can be imposed in succession when each step preserves the earlier ones. -/
lemma collect_conditions {ι X : Type*} (S : Finset ι) {P : X → Prop} {C : ι → X → Prop}
    (base : ∃ x, P x) (step : ∀ i ∈ S, ∀ x, P x → ∃ y, P y ∧ C i y ∧ ∀ j, C j x → C j y) :
    ∃ x, P x ∧ ∀ i ∈ S, C i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using base
  | @insert i S hi ih =>
    obtain ⟨x,hx,h⟩ := ih fun j hj => step j (mem_insert_of_mem hj)
    obtain ⟨y,hy,hi,hxy⟩ := step i (mem_insert_self ..) x hx
    exact ⟨y,hy,by simp_all⟩

theorem synchronize_paths (n : ℕ) (hn : 1 ≤ n) {w : ι → LetterGroup} {lmb μ : ℝ}
    (hp : Path a w lmb) (hm : Path a w μ) (hlmb : 0 < lmb)
    (hratio : μ/lmb < 1/(n:ℝ)) :
    ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path a W (1/(t:ℝ)) := by
  let S := Icc 1 n
  let e (t : ℕ) := 1/(t:ℝ)
  have he (t : ℕ) (ht : t ∈ S) : e t ∈ Set.Icc (μ/lmb) 1 := by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp ht
    exact ⟨hratio.le.trans (by dsimp [e]; gcongr), (div_le_one (by positivity)).mpr (by exact_mod_cast h₁)⟩
  have hh : μ/lmb ≤ 1 := by grind
  have base : ∃ v, Path a v 1 ∧ Path a v (μ/lmb) :=
    ⟨_,by simpa [hlmb.ne'] using hp.scale lmb⁻¹ (by positivity),
      by simpa [div_eq_inv_mul] using hm.scale lmb⁻¹ (by positivity)⟩
  obtain ⟨v,_,hv⟩ := collect_conditions S (C := fun t v => Path a v (e t)) base
    (fun t ht v ⟨hp,hm⟩ => by
      obtain ⟨c,d,hc,hd,hcd,h⟩ := (Convex.mem_Icc hh).mp (he t ht)
      let u := (fun i => scaleGroup c (v i)) * (fun i => scaleGroup d (v i))
      have lift {x : ℝ} (hx : Path a v x) : Path a u x := by
        simpa only [← add_mul,hcd,one_mul] using (hx.scale c hc).mul (hx.scale d hd)
      exact ⟨u,⟨lift hp,lift hm⟩,h ▸ (hm.scale c hc).mul (hp.scale d hd),fun _ => lift⟩)
  aesop
end
end OAI.EuclideanRamsey
