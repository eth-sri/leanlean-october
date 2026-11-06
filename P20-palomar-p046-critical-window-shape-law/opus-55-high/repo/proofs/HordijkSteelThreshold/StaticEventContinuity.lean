module

public import proofs.HordijkSteelThreshold.WordContourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval
open scoped ENNReal

variable (a : I) (P : Prop)

noncomputable def staticAtomWeight  : NNReal :=
  if P then toNNReal a else toNNReal $ σ a

theorem ambientCoordLaw_atom  :
    ambientCoordLaw a {P} = (staticAtomWeight a P : ENNReal) := by
  by_cases hp : P
  · have he := propext (iff_true_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]
  · have he := propext (iff_false_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]

end HordijkSteelThreshold
