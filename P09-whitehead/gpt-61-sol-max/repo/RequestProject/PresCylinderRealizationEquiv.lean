import Mathlib.Tactic

import RequestProject.RankOneCylinderRealization
import RequestProject.PresPosetDimension

/-! The actual topological mapping cylinder in the presentation model
collapses to the subdivided rose. The outer attaching circles are sent
to the exact realization maps reading their prescribed words. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb CategoryTheory


variable {A J : Type} (w : J → List (A × Bool))

def presCylinderRealizationHomotopyEquiv  :=
  rankOneCylinderRealizationHomotopyEquiv (aHom w) (circleDimension w)
    (circleDimension_strictMono w) (circleDimension_le_one w)

end FiniteChains.PresModel
