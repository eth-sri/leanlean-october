module
public import OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalLiveSource
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

def physicalFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  ![Cmain*Z ^(2*δ+ε)*ηNorm*Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*
      profileMoment J₁*profileMoment J₂,
    Cexc*Z ^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*K ^(5/6:ℝ)*
      (loProduct*wlo*wlo)^(-2/3:ℝ),
    Cdiag*K*‖paperRadialFourier W 0‖,
    Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*K*Z ^(-saving)]

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
  pm_8485 SΦ.sup W
  intro j
  fin_cases j <;> dsimp [physicalFactors] <;> positivity

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI
