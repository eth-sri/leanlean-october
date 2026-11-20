module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowCanonicalDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=>divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖eisEmbedding (element C C hC.1 s.columns I)‖^2/X)) θ) z

def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=>divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖eisEmbedding (element C D hD.1 s.columns I)‖^2/X)) θ)) z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
