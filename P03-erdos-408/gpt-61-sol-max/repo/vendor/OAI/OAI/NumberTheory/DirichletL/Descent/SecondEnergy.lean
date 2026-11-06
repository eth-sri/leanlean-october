module

public import OAI.NumberTheory.DirichletL.Inversion.SecondFibers
public import OAI.NumberTheory.DirichletL.Descent.InitializationEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section


abbrev SecondChild := OuterTriple × Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O

def secondChild {Jo Jn } (x : SecondTuple Jo Jn)  :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency)

def secondDivisorWeight (K : ℕ) (c : SecondChild)  :=
  ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4*K) *
    ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2*K) *
    ((idealDivisors c.1.quotient).card : ℝ) ^ (2*K) *
    ((idealDivisors c.1.residual).card : ℝ) ^ (2*K)

end
end SevenEighths.InverseMoment

end OAI
