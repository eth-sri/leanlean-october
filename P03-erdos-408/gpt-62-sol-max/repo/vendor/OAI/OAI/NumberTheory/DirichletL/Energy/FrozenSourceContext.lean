module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
public import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
public import OAI.NumberTheory.DirichletL.Moments.CommonRadialData
public import OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators

@[expose] public section

namespace OAI.SevenEighths.CenteredMomentFrozenSourceContext

noncomputable section
open scoped Classical
open HeckeFamily ConcreteTraceCRT CompletedGauss CanonicalQuadraticSieve
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData ActualEisensteinCubic
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily CenteredMomentCommonAllocationSum
local notation "O" => HeckeFamily.O

/-- The common-label conductor and nonvanishing gates on a frozen allocation. -/
abbrev ForFrozenSources {α : Type*} [Fintype α] (src : Input α)
    (P : ∀ C D : Ideal O, Ideal O → Finset (CommonIndex C D) →
      actualAllocations src.pools C → Character → ℝ → Prop) : Prop :=
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} → P C D R0 E B τ t

end
end OAI.SevenEighths.CenteredMomentFrozenSourceContext
