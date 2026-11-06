module

public import OAI.NumberTheory.DirichletL.Detector.Physical
public import OAI.NumberTheory.DirichletL.Descent.Completion

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion InitialMeanSquare SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

end SevenEighths.ProbePhysical
end

end OAI
