module
public import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPaidScales
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6

def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6

lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤allowance C D Z:=by
  unfold allowance;positivity

lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI
