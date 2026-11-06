module

public import OAI.NumberTheory.DirichletL.Moments.FirstEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstSectors

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI
