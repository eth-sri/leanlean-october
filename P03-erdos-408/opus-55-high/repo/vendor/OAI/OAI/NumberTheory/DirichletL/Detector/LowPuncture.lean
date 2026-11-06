module

public import OAI.NumberTheory.DirichletL.Detector.LowPeriod
public import OAI.NumberTheory.DirichletL.Detector.CalibrationSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve
open RayFourExpansion SecondPassArithmetic
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : ActualEisensteinCubic.O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ConcretePrimeRowBridge.goodLambda∣(calibrationForSet S hS).generator ∧ (2:ActualEisensteinCubic.O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    simp

lemma supported_of_coprime_bad (B n : ActualEisensteinCubic.O) (hBL : ConcretePrimeRowBridge.goodLambda∣B) (hB2 : (2:ActualEisensteinCubic.O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simp_all

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : ActualEisensteinCubic.O)
    (D : GoodMaskRowData B 1 C.generator) (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : ActualEisensteinCubic.O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:ActualEisensteinCubic.O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  simp_all

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : ActualEisensteinCubic.O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : ConcretePrimeRowBridge.goodLambda∣B) (hB2 : (2:ActualEisensteinCubic.O)∣B)
    (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : ActualEisensteinCubic.O) (hpn : ConcretePrimeRowBridge.goodLambda^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : ActualEisensteinCubic.O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  simp

end SevenEighths.ProbePhysical
end

end OAI
