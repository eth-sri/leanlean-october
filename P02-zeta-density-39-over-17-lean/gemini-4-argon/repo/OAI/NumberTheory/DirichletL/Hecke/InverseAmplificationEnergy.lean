module
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤P.val.absNorm := by
    exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)<P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]
