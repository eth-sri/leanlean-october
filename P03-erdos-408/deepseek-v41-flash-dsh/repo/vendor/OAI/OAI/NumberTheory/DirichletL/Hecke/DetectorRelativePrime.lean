module

public import OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
