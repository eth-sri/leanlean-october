/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ClassTruth
public import InfinitaryLogic.Descriptive.SmallVocabularyTransport

@[expose] public section

namespace VaughtConjecture.Knight.StoppingRankFiltration

open FirstOrder Language

/-- The canonical class of a coded model.  No measurability of this map is asserted. -/
noncomputable def modelClass (c : ModelsOf knightSentence) : Classes :=
  isoClassEquiv (Quotient.mk (isoSetoid knightSentence) c)

theorem modelClass_surjective : Function.Surjective modelClass := by
  intro q
  obtain ⟨c, hc⟩ := Quotient.mk_surjective (isoClassEquiv.symm q)
  exact ⟨c, by rw [modelClass, hc, Equiv.apply_symm_apply]⟩

/-- Isomorphic codes have the same class. -/
theorem modelClass_eq_of_iso {c d : ModelsOf knightSentence}
    (h : (structureIsoSetoid knightLang).r c.1 d.1) : modelClass c = modelClass d :=
  congrArg isoClassEquiv (Quotient.sound (isoSetoid_r_iff.mpr h))

/-- **Class truth is satisfaction on the code.** -/
theorem realizes_modelClass (φ : knightLang.Sentenceω) (c : ModelsOf knightSentence) :
    realizes φ (modelClass c) ↔ c.1 ∈ ModelsOf φ := by
  change @Sentenceω.Realize knightLang φ ℕ (structureOf (realizationOfCode c).1) ↔ _
  exact (@LomegaEquiv.of_equiv knightLang ℕ ℕ
    (structureOf (realizationOfCode c).1) c.1.toStructure
    (isKnightModel_of_mem c).structureOfToRealizationEquiv φ).trans
    (FirstOrder.Language.SmallVocabulary.mem_modelsOf_iff_realize knightLang c.1 φ).symm

end VaughtConjecture.Knight.StoppingRankFiltration
