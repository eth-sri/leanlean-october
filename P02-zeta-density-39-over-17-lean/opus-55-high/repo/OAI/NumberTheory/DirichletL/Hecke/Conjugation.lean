module
public import OAI.NumberTheory.DirichletL.Hecke.IdealOperations
public import OAI.NumberTheory.DirichletL.Hecke.Euler
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

section
variable (χ : Character)
include χ
theorem idealCoeff_inverse_conj (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  pm_4915 χ.modulus Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  grind
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

theorem idealTerm_inverse_conj (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)<J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    pm_519 hA hB
    pm_800
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s
end

end SevenEighths.HeckeFamily

end

end OAI
