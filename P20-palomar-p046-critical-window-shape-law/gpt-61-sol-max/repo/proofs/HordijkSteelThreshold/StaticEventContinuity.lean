
import proofs.HordijkSteelThreshold.WordContourProbability




namespace HordijkSteelThreshold
open Classical unitInterval

variable (a : I) (P : Prop)

noncomputable def staticAtomWeight   :=
  if P then toNNReal a else toNNReal (σ a)

theorem ambientCoordLaw_atom  :
    ambientCoordLaw a {P} = staticAtomWeight a P := by simp_all [ambientCoordLaw, staticAtomWeight] ; aesop

end HordijkSteelThreshold
