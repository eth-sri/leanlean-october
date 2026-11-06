module

public import OAI.NumberTheory.DirichletL.Moments.HeckeCancellation
public import OAI.NumberTheory.DirichletL.Moments.Height

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.CenteredMomentHeckeTwist
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentLattice CenteredMomentCounting CenteredMomentTwist
open EisensteinSchwartzPoisson

def twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal ActualEisensteinCubic.O, idealCoeff χ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem idealSum_absolute (χ : Character) (W : ℝ → ℂ) (b M X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖idealSum χ W X‖ ≤ (128*b*M)*X := by
  have h := norm_tsum_ideal_ball (fun I => idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) M (by positivity) hM (by change idealCoeff χ (0:Ideal ActualEisensteinCubic.O)*_ = 0; grind)
    (by intro I; rw [norm_mul]; exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by intro I hI; apply (div_le_iff₀ hX).mp; simp_all)
  change ‖idealSum χ W X‖ ≤ _ at h
  linarith

theorem twistedIdealSum_scale (χ : Character) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedIdealSum χ W t X = (X : ℂ) ^ (Complex.I * t) *
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedIdealSum idealSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  grind

theorem twistedIdealSum_volume (η χ ψ : Character) (Q : Ideal ActualEisensteinCubic.O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : ActualEisensteinCubic.O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (by grind))

theorem twistedIdealSum_absolute (χ : Character) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact idealSum_absolute χ _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (by grind))

theorem twisted_actual_volumeCoefficient_norm_le (η χ ψ : Character) (Q : Ideal ActualEisensteinCubic.O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : ActualEisensteinCubic.O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (by grind)
  exact norm_linear_coefficient_le (fun X => idealSum χ V X)
    _ (128 * b * M) (volumeControl Q χ V) (volumeControl_nonneg Q χ V)
    (fun X hX => actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow V b X hX hV)
    (fun X hX => idealSum_absolute χ V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem actual_twisted_rectangle_saving
    (η χ ψ : Character) (Q : Ideal ActualEisensteinCubic.O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : ActualEisensteinCubic.O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
      twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := volumeControl Q χ V₁ + volumeControl Q χ V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := volumeControl_nonneg Q χ V₁
  have hE₂ := volumeControl_nonneg Q χ V₂
  have hE : 0 ≤ E := by positivity
  have hC : 0 ≤ C := by positivity
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (by linarith)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (by linarith)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (by linarith)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (by linarith)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_actual_volumeCoefficient_norm_le η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X‖ ≤ C * X :=
    (twistedIdealSum_absolute χ W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (by linarith)).trans (mul_le_mul_of_nonneg_right hC₂ (by linarith))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (by linarith) (by linarith)
      (by linarith) (by linarith) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (by grind) (by grind)
    (by grind) (by grind) (by grind) (by grind)
    (by grind) (by grind) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeTwist

end

end OAI
