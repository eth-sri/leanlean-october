module
public import OAI.NumberTheory.DirichletL.Hecke.Reciprocal
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  pm_212 hI I CubicEisenstein.fullIdealWeight
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  pm_3116 hs0 s hs1
  pm_8744 hsp
  pm_8629 hs0 hsp hs1
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  pm_1280
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

end

end OAI
