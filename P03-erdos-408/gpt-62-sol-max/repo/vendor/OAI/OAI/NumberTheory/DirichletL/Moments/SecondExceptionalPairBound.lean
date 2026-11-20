module

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairDictionary
public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic


@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O):ℝ:=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)


end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI
