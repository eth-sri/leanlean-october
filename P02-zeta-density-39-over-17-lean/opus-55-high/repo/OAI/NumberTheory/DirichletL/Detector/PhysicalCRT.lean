module
public import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalRowCompletion GaussianShiftedPartition
open CanonicalQuadraticSieve CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentFirstPoisson CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem coprime_function_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (Fa : Residue a → ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      Fa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      (∑ x : Residue a, Fa (Ideal.Quotient.mk _ b*x) *
        quotientTrace a ha (frequencyReduction a (a*b) (dvd_mul_right a b) h*x)) *
      (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
        quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  pm_3894
  pm_2989
  simp only [ he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, ]
  pc_200 Finset.mul_sum Finset.sum_mul
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sexticGauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (H : O) :
    sexticGauss (a*b) (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)) H =
      idealRowHom b (Ideal.span {a}) * idealRowHom a (Ideal.span {b}) *
        sexticGauss a (supportedElement_ne_zero a ha) H *
        sexticGauss b (supportedElement_ne_zero b hb) H := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let := finite_quotient_span (supportedElement_ne_zero b hb)
  let := finite_quotient_span (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb))
  pm_2956
  pm_458 Residue a b
  have he := coprime_character_fourier a b (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)
    hcop (supportedModulusCharacter a ha) (supportedModulusCharacter b hb) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk,
    residueGauss_supported_mk] at he
  rw [← he]
  pm_3809 sexticGauss tsum_fintype x hx
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sexticGauss_coefficient_mk]
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk]
  congr 1
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma elementFourier_const_mul (c : O) (hc : c≠0) (F : O → ℂ) (H : O) (B : ℂ) :
    elementFourier c hc (fun m => B*F m) H = B*elementFourier c hc F H := by
  simp only [elementFourier, mul_assoc, tsum_mul_left]

section
variable (A B s r : O)
include A B s r
lemma bareMoving_product (hs : Supported (Ideal.span {s}))
    (hr : Supported (Ideal.span {r})) (hcop : IsCoprime s r) (m : O) :
    idealRowHom m (Ideal.span {A*B}) *
      sexticGauss (s*r) (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) (-m) =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      ((idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) := by
  rw [sexticGauss_coprime_product s r hs hr hcop]
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  ring

theorem barePhysicalFourier_product (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    barePhysicalFourier (A*B) (s*r) (mul_ne_zero hA hB)
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
  have hsc : IsCoprime s r := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B*r) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A*s) r := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  have hBr := mul_ne_zero hB (supportedElement_ne_zero r hr)
  pm_5920 hAs hBr
  pm_458 Residue A s
  pm_458 Residue B r
  let : Fintype (Residue ((A*s)*(B*r))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A*s) (B*r) hAs hBr hcop
    (movingQuotient A s (supportedElement_ne_zero s hs))
    (movingQuotient B r (supportedElement_ne_zero r hr)) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk] at he
  simp_rw [movingQuotient_unit_scale A s hs (B*r) hc1,
    movingQuotient_unit_scale B r hr (A*s) hc2, mul_assoc] at he
  simp only [← Finset.mul_sum] at he
  have hexpand : elementFourier ((A*s)*(B*r)) (mul_ne_zero hAs hBr)
      (fun m => (idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) H =
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmk := representative_spec ((A*s)*(B*r)) x
        have hred1 : frequencyReduction (A*s) ((A*s)*(B*r)) (dvd_mul_right _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        have hred2 : frequencyReduction (B*r) ((A*s)*(B*r)) (dvd_mul_left _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        rw [hred1, hred2, movingQuotient_mk, movingQuotient_mk]
        ring
      _ = _ := he
      _ = _ := by
        pm_3523 barePhysicalFourier elementFourier movingQuotient tsum_fintype
  simp only [barePhysicalFourier] at hexpand
  unfold barePhysicalFourier
  rw [elementFourier_congr ((A*B)*(s*r)) ((A*s)*(B*r)) _ (mul_ne_zero hAs hBr) _ H (by ring)]
  simp_rw [bareMoving_product A B s r hs hr hsc]
  rw [elementFourier_const_mul, hexpand]
  ring

theorem bareCongruenceCoefficient_product (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  have he := barePhysicalFourier_product A B s r hA hB hs hr hcop H
  simp only [barePhysicalFourier_eq] at he
  have hnorm : Ideal.absNorm (Ideal.span {s*r}) =
      Ideal.absNorm (Ideal.span {s}) * Ideal.absNorm (Ideal.span {r}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, Nat.cast_mul] at he
  pm_3847 hns s hs
  pm_3847 hnr r hr
  apply mul_left_cancel₀ (mul_ne_zero hns hnr)
  rw [he]
  ring
end

lemma idealRowHom_ne_zero_of_coprime (s a : O)
    (hs : Supported (Ideal.span {s})) (hc : IsCoprime s a) :
    idealRowHom a (Ideal.span {s})≠0 := by
  rw [← supportedModulusCharacter_mk s hs a]
  exact (supportedModulusCharacter s hs).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff s a).mpr hc)

theorem bareCongruenceCoefficient_product_reduced (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  rw [bareCongruenceCoefficient_product A B s r hA hB hs hr hcop H]
  have hsr := idealRowHom_ne_zero_of_coprime s r hs
    hcop.of_mul_left_right.of_mul_right_right
  have hrs := idealRowHom_ne_zero_of_coprime r s hr
    hcop.of_mul_left_right.of_mul_right_right.symm
  have hsB := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  simp only [idealRowHom_argument_mul]
  field_simp

end SevenEighths.ProbePhysical

end OAI
