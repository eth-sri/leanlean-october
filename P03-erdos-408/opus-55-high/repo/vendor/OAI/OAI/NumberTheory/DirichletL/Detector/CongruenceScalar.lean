module

public import OAI.NumberTheory.DirichletL.Detector.Sextic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open GaussianShiftedPartition

def exactQuotient (a b : ActualEisensteinCubic.O) (h : b ∣ a) : ActualEisensteinCubic.O := Classical.choose h

lemma exactQuotient_spec (a b : ActualEisensteinCubic.O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : ActualEisensteinCubic.O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

def positiveScalar (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : ActualEisensteinCubic.O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dite_eq_right]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by positivity)).mul_right _
  have hunit : p ∣ (1:ActualEisensteinCubic.O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dite_eq_left hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : ActualEisensteinCubic.O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  simp_all

end SevenEighths.ProbePrimePower
end

end OAI
