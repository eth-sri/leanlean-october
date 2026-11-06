module

public import OAI.NumberTheory.DirichletL.Detector.PhasePowers

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open CanonicalRowCompletion

def sexticPair (p q : ActualEisensteinCubic.O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

end SevenEighths.ProbePhase
end

end OAI
