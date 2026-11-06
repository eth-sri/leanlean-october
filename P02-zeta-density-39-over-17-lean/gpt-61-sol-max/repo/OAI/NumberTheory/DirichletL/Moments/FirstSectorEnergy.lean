module
public import OAI.NumberTheory.DirichletL.Moments.FirstEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstSectors

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic


open CenteredMomentCommonSectors CenteredMomentCompleteCommon

open IdealMobiusDivisorSum
open scoped EisensteinO

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)






