module

public import OAI.NumberTheory.DirichletL.Moments.FirstEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstSectors

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open CenteredMomentCommonSectors CenteredMomentCompleteCommon
open IdealMobiusDivisorSum

theorem fixed_common_parts (C D : Ideal ActualEisensteinCubic.O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI
