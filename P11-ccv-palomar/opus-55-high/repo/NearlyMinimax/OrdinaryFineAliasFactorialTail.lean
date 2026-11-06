module

public import NearlyMinimax.OrdinaryFineAliasAggregation
public import NearlyMinimax.AliasTailSummation
public import RoughRegime.Macro

𝗌

/-! The actual response-summed ordinary fine-alias factorial tail at the
paper's canonical rounded saddle. The fixed exp(L M) changes only the
factorial-tail constant and never the source activity exponent. -/
𝛅
open scoped BigOperators Topology
𝚨
𝚩
𝛆
𝚬

def ordinaryFineAliasSaddleCoefficient (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleCoefficient s d $ densityIntervalExponent ad bd

def ordinaryFineAliasSaddleTheta (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleTheta s d $ densityIntervalExponent ad bd

𝗇 𝔄 densityIntervalExponent ad bd+1
𝗃 𝔅 ἀ s d ad bd
def ordinaryFineAliasSaddleTargetBound (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℕ :=
  lowerAliasFineTargetBound d 𝔅 ordinaryFineAliasSaddleTheta 𝔄

def ordinaryFineAliasSaddleTailPrefactor (s : ℝ) (d q : ℕ) (ad bd C a rho : ℝ) : ℝ :=
  ordinaryAliasFamilySpatialPrefactor d q 𝔅 ordinaryFineAliasSaddleTargetBound
    ad bd 𝔄 C a rho

def ordinaryFineAliasSaddleTailExponent (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerAliasSpatialFixedL d 𝔅 ordinaryFineAliasSaddleTheta 𝔄

/-- Chosen once before the sample size, observation count, frame degree or
any nuisance tuple. -/
def ordinaryFineAliasFactorialConstant (s : ℝ) (d q : ℕ) (ad bd C a rho Csharp : ℝ) : ℝ :=
  aliasTailConstant (ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd) 𝔅 ordinaryFineAliasSaddleTailExponent

theorem ordinaryFineAliasFactorialConstant_ge_one
    (hbd : 0 ≤ bd) (hCs : 0 ≤ Csharp) :
    1 ≤ ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp := aliasTailConstant_ge_one (ordinaryAliasFamilySpatialPrefactor_nonneg ..)
    hCs $ by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
