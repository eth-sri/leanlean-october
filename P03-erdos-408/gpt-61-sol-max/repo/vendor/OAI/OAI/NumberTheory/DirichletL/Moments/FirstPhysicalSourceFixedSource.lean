module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowCanonical
public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy FourierBridge

variable {ι:Type*}[Fintype ι]


variable {η:Character}{C D:Ideal ActualEisensteinCubic.O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

section
variable (F:FixedPair η C D hC E ξ₁ ξ₂)

theorem FixedPair.left_column  (s:OriginalData ι) t  L 
     I :
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column  (hD:Supported D)
    (s:OriginalData ι) t  L  I :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

end

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
