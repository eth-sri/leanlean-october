module

public import OAI.NumberTheory.DirichletL.Detector.LiftedFourier
public import OAI.NumberTheory.DirichletL.Detector.Physical

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower

def rawFourier (a : ActualEisensteinCubic.O) (ha : a≠0) (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (H : ActualEisensteinCubic.O) : ℂ :=
  ∑' m : ActualEisensteinCubic.O ⧸ Ideal.span {a}, F m * quotientTrace a ha (Ideal.Quotient.mk _ H * m)

theorem rawFourier_exactQuotient (a s : ActualEisensteinCubic.O) (ha : a≠0) (hs : s≠0)
    (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (H : ActualEisensteinCubic.O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dite_eq_left h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dite_eq_right h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

def congruenceCoefficient (a s : ActualEisensteinCubic.O) (ha : a≠0)
    (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (χ : (ActualEisensteinCubic.O ⧸ Ideal.span {s}) → ℂ) (H : ActualEisensteinCubic.O) : ℂ :=
  ∑' d : ActualEisensteinCubic.O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

lemma trace_split_product (a s : ActualEisensteinCubic.O) (ha : a≠0) (hs : s≠0) (H m d : ActualEisensteinCubic.O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

def fullFourier (a s : ActualEisensteinCubic.O) (ha : a≠0) (hs : s≠0)
    (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (χ : (ActualEisensteinCubic.O ⧸ Ideal.span {s}) → ℂ) (H : ActualEisensteinCubic.O) : ℂ :=
  ∑' m : ActualEisensteinCubic.O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

theorem fullFourier_eq_congruence (a s : ActualEisensteinCubic.O) (ha : a≠0) (hs : s≠0)
    (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (χ : (ActualEisensteinCubic.O ⧸ Ideal.span {s}) → ℂ) (H : ActualEisensteinCubic.O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {a*s}) := finite_quotient_span (by positivity)
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

theorem rawFourier_norm_le (a : ActualEisensteinCubic.O) (ha : a≠0) (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : ActualEisensteinCubic.O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span ha
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : ActualEisensteinCubic.O ⧸ Ideal.span {a}, ‖F m * quotientTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : ActualEisensteinCubic.O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      simp_all
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem congruenceCoefficient_norm_le (a s : ActualEisensteinCubic.O) (ha : a≠0) (hs : s≠0)
    (F : (ActualEisensteinCubic.O ⧸ Ideal.span {a}) → ℂ) (χ : (ActualEisensteinCubic.O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : ActualEisensteinCubic.O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span hs
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : ActualEisensteinCubic.O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : ActualEisensteinCubic.O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (by grind) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      simp
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]

end SevenEighths.ProbePhysical
end

end OAI
