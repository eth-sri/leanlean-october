module

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairDictionary
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalWindow
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowHeight

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:HeckeFamily.O)
    (C D)(hC:Supported C)(hD:Supported D)(R seed:Ideal HeckeFamily.O)
    (t w X Y:ℝ)(Ds:Finset (Ideal HeckeFamily.O))(rows:Finset HeckeFamily.O):=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal HeckeFamily.O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal HeckeFamily.O):ℝ)/Y)) w)) (-z)‖)

omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι) τ η  v t θ X  C  hC 
     R seed L  V  z :
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI
