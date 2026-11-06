module

public import RequestProject.Oriented
public import RequestProject.RankOneCylinderRealization
public import RequestProject.PresPosetDimension

@[expose] public section

/-! The actual topological mapping cylinder in the presentation model
collapses to the subdivided rose. The outer attaching circles are sent
to the exact realization maps reading their prescribed words. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb CategoryTheory
open scoped Topology

variable {A J : Type} (w : J → FiniteChains.Comb.Oriented A)

def presCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylBase w))
      (orderNerveRealization (Rose A)) :=
  rankOneCylinderRealizationHomotopyEquiv (aHom w) (circleDimension w)
    (circleDimension_strictMono w) (circleDimension_le_one w)

end FiniteChains.PresModel
