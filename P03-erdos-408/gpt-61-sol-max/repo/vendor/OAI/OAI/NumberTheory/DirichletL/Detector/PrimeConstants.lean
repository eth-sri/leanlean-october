module

public import OAI.NumberTheory.DirichletL.Detector.PrimePhase

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def localGamma (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (r : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ r)

lemma localGamma_norm_one  p   hp  [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
     r  (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 :=
  MixedGaussConversion.norm_localGauss p hp hg hc r hr hr6

section
variable (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P)
include P hg

lemma actualSextic_six    
      (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

lemma actualSextic_neg_one_sq    
      : actualSextic P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

end

theorem localGamma_one_two_signal  p   hp 
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg := by
  have he := breveGamma1_gamma2_eq_neg_alpha_G (Ideal.span {p}) hg hc p rfl hp hprimary
  simpa only [localGamma, ConcreteBreveE.normalizedTraceGauss, pow_one,
    breveGamma1, breveGamma2, MixedGaussConversion.localG, FiniteGaussPhase.angularFactor,
    neg_div] using he

section
variable (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
include P hg hc

lemma actualSextic_pow_six_mul_add    
         r j  :
    actualSextic P hg ^ (6*r+j) = actualSextic P hg ^ j := by
  rw [pow_add, pow_mul, actualSextic_six P hg hc, one_pow, one_mul]

lemma actualSextic_fifth_inverse    
        :
    actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact actualSextic_six P hg hc

end

lemma primeGauss_inverse_pair  p   hp 
    [(Ideal.span {p} : Ideal O).IsMaximal]
     χ  (hχ : χ ≠ 1) :
    primeGauss p hp χ 1 * primeGauss p hp χ⁻¹ 1 =
      χ (-1) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have ht := ProbeGauss.gauss_inverse_pair χ (quotientTrace p hp) hχ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [primeGauss, tsum_fintype, map_one, one_mul, gaussSum,
    ← Nat.card_eq_fintype_card, hcard] using ht

end SevenEighths.ProbePrimePower
end

end OAI
