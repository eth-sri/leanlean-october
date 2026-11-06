module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowCanonical
public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstFixedSourceDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
