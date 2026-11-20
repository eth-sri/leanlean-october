module

public import NearlyMinimax.OrdinaryFineAliasAggregation
public import NearlyMinimax.AliasTailSummation

@[expose] public section

/-! The actual response-summed ordinary fine-alias factorial tail at the
paper's canonical rounded saddle. The fixed exp(L M) changes only the
factorial-tail constant and never the source activity exponent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

section
variable (s : ℝ) (d q : ℕ) (ad bd C a rho Csharp : ℝ)

def ordinaryFineAliasSaddleCoefficient : ℝ :=
  lowerSaddleCoefficient s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTheta : ℝ :=
  lowerSaddleTheta s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTargetBound : ℕ :=
  lowerAliasFineTargetBound d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)

def ordinaryFineAliasSaddleTailPrefactor : ℝ :=
  ordinaryAliasFamilySpatialPrefactor d q (ordinaryFineAliasSaddleTargetBound s d ad bd)
    ad bd (densityIntervalExponent ad bd+1) C a rho

def ordinaryFineAliasSaddleTailExponent : ℝ :=
  lowerAliasSpatialFixedL d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)

/-- Chosen once before the sample size, observation count, frame degree or
any nuisance tuple. -/
def ordinaryFineAliasFactorialConstant : ℝ :=
  aliasTailConstant (ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd) (ordinaryFineAliasSaddleTailExponent s d ad bd)

end

end NearlyMinimax
