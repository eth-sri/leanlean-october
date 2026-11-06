module
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
public import OAI.NumberTheory.DirichletL.Hecke.Conjugation
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simp_all

theorem conj_shift (σ freq : ℝ) : conj (shift σ freq)=shift σ (-freq) := by
  pm_382 HeckeDyadic.shift map_sub map_mul conj_ofReal conj_I ofReal_neg
  ring

section
variable (χ : Character) (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D)
include χ inv W D σ freq hD
theorem conj_polynomial :
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

theorem polynomial_inverse_norm :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]
end

theorem conjugate_profile_support (W : ℝ→ℂ) :
    Function.support (fun x => conj (W x))=Function.support W := by aesop

theorem conjugate_profile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := by
  exact Complex.conjCLE.contDiff.comp hW

end SevenEighths.HeckeInverseAmplification

end

end OAI
