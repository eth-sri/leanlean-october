module

public import OAI.NumberTheory.DirichletL.Detector.Physical
public import OAI.NumberTheory.DirichletL.Descent.Completion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic

local notation "Id" => Ideal ActualEisensteinCubic.O

def physicalRowBase (η : HeckeFamily.Character) (Xi : ActualEisensteinCubic.O→*ℂ)
    (s ) (hs : Supported (Ideal.span {s}))  :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

end SevenEighths.ProbePhysical
end

end OAI
