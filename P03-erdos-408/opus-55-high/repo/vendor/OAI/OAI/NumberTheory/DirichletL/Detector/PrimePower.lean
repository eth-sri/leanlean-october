module

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Detector.Gauss

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open CubicEisenstein


def primeGauss (p : ActualEisensteinCubic.O) (hp : p ≠ 0) (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ)
    (h : ActualEisensteinCubic.O) : ℂ :=
  ∑' x : ActualEisensteinCubic.O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

theorem primePowerGauss_support (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (by positivity) χ h hG

theorem primePowerGauss_zero_off_support (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  simp

theorem primePowerGauss_nonprincipal_extra_divisibility (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : ActualEisensteinCubic.O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  simp_all

theorem primePowerGauss_principal (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : ActualEisensteinCubic.O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (ActualEisensteinCubic.O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (χ ξ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : ActualEisensteinCubic.O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · simp_all
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ ξ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∑' d : ActualEisensteinCubic.O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (χ ξ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : ActualEisensteinCubic.O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : ActualEisensteinCubic.O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : ActualEisensteinCubic.O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    grind
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI
