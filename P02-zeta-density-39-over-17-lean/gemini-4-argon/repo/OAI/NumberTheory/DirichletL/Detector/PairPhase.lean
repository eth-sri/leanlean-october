module
public import OAI.NumberTheory.DirichletL.Detector.PhasePowers

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})
