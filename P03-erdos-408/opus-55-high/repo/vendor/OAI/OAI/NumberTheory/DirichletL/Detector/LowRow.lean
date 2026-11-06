module

public import OAI.NumberTheory.DirichletL.Detector.Physical
public import OAI.NumberTheory.DirichletL.Descent.Completion

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve
open InitialMeanSquare
local notation "Id" => Ideal ActualEisensteinCubic.O

def physicalRowBase (η : HeckeFamily.Character) (Xi : ActualEisensteinCubic.O→*ℂ)
    (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s})) : ActualEisensteinCubic.O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

end SevenEighths.ProbePhysical
end

end OAI
