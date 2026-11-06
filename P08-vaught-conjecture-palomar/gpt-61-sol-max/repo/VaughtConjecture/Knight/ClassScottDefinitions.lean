/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ClassPresentation
import InfinitaryLogic.Descriptive.ScottDefinability

/-! # Scott sentences define every countable set of classes

This is the ordinary Scott-sentence argument through the sentence/model
correspondence. It uses no receiving, classification or rank analysis. In
particular countable disjunction includes empty and finite sets, and it asserts
neither effective enumeration nor a measurable choice of Scott sentences.
-/

namespace VaughtConjecture.Knight.StoppingRankFiltration
open FirstOrder Language

/-- Ordinary Scott sentences isolate each class among the actual Knight models
(`InfinitaryLogic`'s `isolatedPresentation_of_surjective` on the class presentation).
This does not assign an effective or measurable Scott sentence to classes. -/
def exists_isolating_sentence q :=
  isolatedPresentation_of_surjective (fun c => c.1) modelClass
    modelClass_surjective (fun _ _ h => modelClass_eq_of_iso h) realizes realizes_modelClass q

