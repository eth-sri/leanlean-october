module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
public import OAI.NumberTheory.DirichletL.Hecke.Conjugation
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale

@[expose] public section

namespace OAI


open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

section
variable (χ : Character) (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D)

theorem coefficient_inverse_conj      J  :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift   : conj (shift σ freq)=shift σ (-freq) := by
  simp_all [HeckeDyadic.shift]

include hD in
theorem conj_polynomial      
        :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

include hD in
theorem polynomial_inverse_norm      
        :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

theorem conjugate_profile_support   :
    Function.support (fun x => conj (W x))=Function.support W := by
  ext x
  simp

theorem conjugate_profile_smooth   (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := Complex.conjCLE.contDiff.comp hW

end

end SevenEighths.HeckeInverseAmplification



end OAI
