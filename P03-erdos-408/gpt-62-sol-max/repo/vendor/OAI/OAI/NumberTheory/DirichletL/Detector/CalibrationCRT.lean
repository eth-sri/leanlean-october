module

public import OAI.NumberTheory.DirichletL.Moments.FirstPoisson
public import OAI.NumberTheory.DirichletL.Detector.CalibrationFourier
public import OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem coprime_mixed_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss a ha χa (frequencyReduction a (a*b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
          quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  rw [coprime_function_fourier a b ha hb hcop χa F h]
  simp only [map_mul, mul_assoc, ← Finset.mul_sum, residueGauss, tsum_fintype]

theorem calibration_mixed_fourier (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) =
      C.residueMonoid b * star (C.residueMonoid H) * (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        (∑' y : Residue b, F (Ideal.Quotient.mk _ C.generator*y) *
          quotientTrace b hb (Ideal.Quotient.mk _ H*y)) := by
  dsimp only
  let C := calibrationForSet S hS
  let := finite_quotient_span C.generator_ne_zero
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero C.generator_ne_zero hb)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator*b)) := Fintype.ofFinite _
  rw [tsum_fintype, coprime_mixed_fourier _ _ C.generator_ne_zero hb hcop]
  change C.residueMonoid b * calibrationGauss C H * _ = _
  rw [calibrationForSet_gauss]
  rw [tsum_fintype]
  dsimp only [C]
  simp only [frequencyReduction_mk]
  ring

theorem calibration_mixed_fourier_zero (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) = 0 := by
  dsimp only
  rw [calibration_mixed_fourier S hS b hb hcop F H]
  have hz : (calibrationForSet S hS).residueMonoid H=0 := by
    change (calibrationForSet S hS).residue (Ideal.Quotient.mk _ H)=0
    apply MulChar.map_nonunit
    exact fun h => hH ((isUnit_quotient_span_iff _ _).mp h)
  rw [hz, star_zero]
  ring

end SevenEighths.ProbePhysical
end

end OAI
