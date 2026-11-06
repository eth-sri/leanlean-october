module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff  χ ψ 
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
     inv   W   D σ freq  :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ)  := if reverse then -freq else freq

theorem norm_of_oriented_coefficients  χ ψ   reverse 
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
     inv   W   D σ freq  (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · solve_by_elim [polynomial_eq_of_idealCoeff]
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    aesop

theorem orientedFrequency_abs  reverse   freq  :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
