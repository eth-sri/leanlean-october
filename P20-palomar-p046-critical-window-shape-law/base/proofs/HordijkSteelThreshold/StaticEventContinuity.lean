module

public import proofs.HordijkSteelThreshold.WordContourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval
open scoped ENNReal

noncomputable def staticAtomWeight (a : I) (P : Prop) : NNReal :=
  if P then toNNReal a else toNNReal (σ a)

theorem ambientCoordLaw_atom (a : I) (P : Prop) :
    ambientCoordLaw a {P} = (staticAtomWeight a P : ENNReal) := by
  by_cases hp : P
  · have he : P = True := propext (iff_true_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]
  · have he : P = False := propext (iff_false_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]

end HordijkSteelThreshold
