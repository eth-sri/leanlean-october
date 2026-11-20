/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ClassPresentation
public import InfinitaryLogic.Descriptive.ScottDefinability

@[expose] public section

namespace VaughtConjecture.Knight.StoppingRankFiltration

open FirstOrder Language

/-- Ordinary Scott sentences isolate each class among the actual Knight models
(`InfinitaryLogic`'s `isolatedPresentation_of_surjective` on the class presentation).
This does not assign an effective or measurable Scott sentence to classes. -/
theorem exists_isolating_sentence (q : Classes) :
    ∃ φ : knightLang.Sentenceω, ∀ s : Classes, realizes φ s ↔ s = q :=
  isolatedPresentation_of_surjective (fun c : ModelsOf knightSentence => c.1) modelClass
    modelClass_surjective (fun _ _ h => modelClass_eq_of_iso h) realizes realizes_modelClass q

end VaughtConjecture.Knight.StoppingRankFiltration
