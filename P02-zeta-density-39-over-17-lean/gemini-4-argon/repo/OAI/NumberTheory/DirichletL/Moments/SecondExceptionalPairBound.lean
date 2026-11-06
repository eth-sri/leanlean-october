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
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairDictionary
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

omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι)(τ η:Character)(v t θ X:ℝ)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(V:ℝ→ℂ)(z:O):
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl
