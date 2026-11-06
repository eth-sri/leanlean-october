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
variable (s : ℝ) (d : ℕ)
include s d

def ordinaryFineAliasSaddleCoefficient  ad bd  :=
  lowerSaddleCoefficient s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTheta  ad bd  :=
  lowerSaddleTheta s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTargetBound  ad bd  :=
  lowerAliasFineTargetBound d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)
end


def ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho  :=
  ordinaryAliasFamilySpatialPrefactor d q (ordinaryFineAliasSaddleTargetBound s d ad bd)
    ad bd (densityIntervalExponent ad bd+1) C a rho

def ordinaryFineAliasSaddleTailExponent s d ad bd  :=
  lowerAliasSpatialFixedL d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)

/-- Chosen once before the sample size, observation count, frame degree or
any nuisance tuple. -/
def ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp  :=
  aliasTailConstant (ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd) (ordinaryFineAliasSaddleTailExponent s d ad bd)

theorem ordinaryFineAliasFactorialConstant_ge_one {s ad bd C a rho Csharp } {d q }
    (hbd : 0 ≤ bd) (hCs : 0 ≤ Csharp) :
    1 ≤ ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp := aliasTailConstant_ge_one (ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)
    hCs (by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity)

end NearlyMinimax
