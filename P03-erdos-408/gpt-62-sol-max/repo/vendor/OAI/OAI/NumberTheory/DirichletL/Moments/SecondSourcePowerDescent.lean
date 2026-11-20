module

public import OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
public import OAI.NumberTheory.DirichletL.Moments.SecondLocalization
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondNonexceptionalAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit
open CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic MeasureTheory UniqueFactorizationMonoid
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

def physicalFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  ![Cmain*Z^(2*δ+ε)*ηNorm*Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*
      profileMoment J₁*profileMoment J₂,
    Cexc*Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*K^(5/6:ℝ)*
      (loProduct*wlo*wlo)^(-2/3:ℝ),
    Cdiag*K*‖paperRadialFourier W 0‖,
    Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*K*Z^(-saving)]

lemma physicalFactors_nonneg (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ))
    (hm : 0≤Cmain) (he : 0≤Cexc) (hd : 0≤Cdiag) (ht : 0≤Ctail)
    (hZ : 0≤Z) (hK : 0≤K) (hη : 0≤ηNorm) (hl : 0≤loProduct) :
    ∀j,0≤physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
      loProduct wlo J₁ J₂ SΦ W j := by
  have hp1:=profileMoment_nonneg J₁
  have hp2:=profileMoment_nonneg J₂
  have hheight:=(heightEnvelope_pos t).le
  have hlo : 0≤loProduct*wlo*wlo := by nlinarith [mul_nonneg hl (sq_nonneg wlo)]
  have hs : 0≤SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  intro j
  fin_cases j <;> dsimp [physicalFactors] <;> positivity

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI
