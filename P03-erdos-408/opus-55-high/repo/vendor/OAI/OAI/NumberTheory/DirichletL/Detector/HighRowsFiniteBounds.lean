module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsTermBounds
public import OAI.NumberTheory.DirichletL.Detector.EulerRegion

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ConcretePrimeRowBridge
variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)

end SevenEighths.ProbeEuler
end

end OAI
