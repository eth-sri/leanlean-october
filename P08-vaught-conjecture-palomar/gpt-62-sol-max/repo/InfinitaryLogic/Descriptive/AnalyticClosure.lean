/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α]

/-- **The off-diagonal of an analytic set is analytic** in a Hausdorff space: if `P` is the range
of a continuous `f` on a Polish space, then `P.offDiag` is the image under `Prod.map f f` of the
open set of pairs with distinct values. -/
protected theorem AnalyticSet.offDiag [T2Space α] {P : Set α} (hP : AnalyticSet P) :
    AnalyticSet P.offDiag := by
  obtain ⟨β, hβt, hβp, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hP
  have hopen : IsOpen {q : β × β | f q.1 ≠ f q.2} :=
    (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)).isOpen_compl
  have : (Set.range f).offDiag = Prod.map f f '' {q | f q.1 ≠ f q.2} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, h⟩
      exact ⟨(a, b), h, rfl⟩
    grind
  rw [this]
  exact hopen.analyticSet_image (hf.prodMap hf)

end MeasureTheory
