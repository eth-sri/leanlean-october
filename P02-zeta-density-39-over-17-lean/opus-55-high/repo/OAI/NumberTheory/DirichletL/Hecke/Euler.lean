module
public import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
public import OAI.NumberTheory.DirichletL.IdealEuler
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

section
variable (χ : Character)
include χ
theorem idealCoeff_norm_le_one (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  pm_4915 χ.modulus Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  grind
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  pm_7124 IdealEuler.series_ne_zero

theorem inverseSeries_mul_LFunction {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  pm_7124 IdealEuler.inverseSeries_mul_series
end

end SevenEighths.HeckeFamily

end

end OAI
