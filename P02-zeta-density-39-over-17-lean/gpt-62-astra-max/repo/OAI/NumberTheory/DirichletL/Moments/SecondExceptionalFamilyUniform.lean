module
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

def fixedExpandedCost : ℝ :=
  1296*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI
