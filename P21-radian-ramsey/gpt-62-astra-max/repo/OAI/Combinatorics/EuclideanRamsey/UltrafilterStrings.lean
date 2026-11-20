/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathWords
public import OAI.Combinatorics.EuclideanRamsey.CornerGroup

@[expose] public noncomputable section

namespace OAI.EuclideanRamsey
open Filter

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

variable {ι : Type*} {a : ι → ℂ}

/-- Every choice of a neighborhood in each coordinate contains a string family.
This property composes directly under ultrafilter multiplication. -/
def Realizes (a : ι → ℂ) (U : ι → Ultrafilter Strings) (q : ℝ) :=
  ∀ B : ι → Set Strings, (∀ i, B i ∈ U i) → ∃ l : List Sim, energy l = q ∧ ∀ i, word (a i) l ∈ B i

lemma Realizes.common [Finite ι] (U : Ultrafilter Strings) : Realizes a (fun _ => U) 0 := by
  intro B h
  obtain ⟨x,hx⟩ := (eventually_all.mpr h).exists
  refine ⟨x.toList.map (fun b => (0,b)),by simp [energy,Function.comp_def],fun i => ?_⟩
  simpa [word,value,Function.comp_def] using (show x ∈ B i from hx i)

lemma Realizes.copy (p : Sim) : Realizes a (fun i => pure (FreeMonoid.of (value (a i) p))) (weight p) :=
  fun _ hh => ⟨[p],by simp [energy],hh⟩

lemma Realizes.mul {U V q t} (hu : Realizes a U q) (hv : Realizes a V t) : Realizes a (U*V) (q+t) := by
  intro B h
  obtain ⟨l,rfl,h⟩ := hu _ (fun i => (Ultrafilter.eventually_mul _ _ _).mp (h i))
  obtain ⟨k,rfl,h⟩ := hv _ h
  exact ⟨l++k,by simp [energy],fun i => by simp [word]; exact h i⟩

/-- Each endpoint has a single ultrafilter profile realizing all its path costs. -/
theorem exists_profiles [Finite ι] (a : ι → ℂ) : ∃ Ψ : LetterGroup → Ultrafilter Strings,
    ∀ {w u}, Path a w u → Realizes a (Ψ ∘ w) u := by
  obtain ⟨p,G,_,φ,hφ⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  choose letter hl using fun z : ℂ => hφ (pure (FreeMonoid.of z))
  let Ψ := φ.comp (letterLift letter).toMulHom
  let q := p*φ (letter 0)⁻¹
  have gen z : Ψ (atom z) = p*pure (FreeMonoid.of z)*q := by simp [Ψ,q,hl,mul_assoc]
  refine ⟨Ψ,fun h => ?_⟩
  induction h with
  | diag g => exact .common (Ψ g)
  | copy b => simpa [Function.comp_def,gen,Pi.mul_def] using
      ((Realizes.common p).mul (Realizes.copy b)).mul (.common q)
  | mul _ _ ih jh => simpa [Function.comp_def,Pi.mul_def,Ψ] using ih.mul jh

end OAI.EuclideanRamsey
