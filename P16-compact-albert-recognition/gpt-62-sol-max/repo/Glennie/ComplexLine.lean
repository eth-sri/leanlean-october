/- Native complex lines and the unit cube-root step for two-slot normalization.
All octonion products are the explicitly declared compact binary operation. -/
module
public import Glennie.Native.Triality
public import Glennie.Native.Statements
public import Mathlib.Analysis.Complex.Polynomial.Basic
@[expose] public section
namespace Glennie
noncomputable section

def octComplexLine (I : Octonion) (z : ℂ) : Octonion :=
  z.re • octScalar 1 + z.im • I

@[simp] theorem octComplexLine_one (I : Octonion) :
    octComplexLine I 1 = octScalar 1 := by simp [octComplexLine]

theorem octComplexLine_mul (I : Octonion) (hi : octRe I = 0)
    (hn : octNormSq I = 1) (z w : ℂ) :
    octComplexLine I (z*w) = octMul (octComplexLine I z) (octComplexLine I w) := by
  have hi2 : octMul I I = (-1 : ℝ) • octScalar 1 := by
    simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self I hi hn
  simp only [octComplexLine, Complex.mul_re, Complex.mul_im,
    octMul_add_left, octMul_add_right, octMul_smul_left, octMul_smul_right,
    octMul_scalar_left, octMul_scalar_right, hi2, one_smul]
  module

theorem octComplexLine_normSq (I : Octonion) (hi : octRe I = 0)
    (hn : octNormSq I = 1) (z : ℂ) :
    octNormSq (octComplexLine I z) = Complex.normSq z := by
  have h := congrArg (fun r : ℝ => z.im^2*r) hn
  simp only [octRe] at hi
  simp [octComplexLine, octNormSq, Quaternion.normSq_def', octScalar,
    Complex.normSq_apply, smul_eq_mul, hi] at h ⊢
  nlinarith [h]

theorem octComplexLine_conj (I : Octonion) (hi : octRe I = 0) (z : ℂ) :
    octConj (octComplexLine I z) = octComplexLine I (star z) := by
  have hI : octConj I = -I := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp_all [octConj, octRe]
  simp only [octComplexLine, octConj_add, octConj_smul, octConj_scalar, hI]
  simp [ smul_neg]

/-- Every native octonion lies in an explicitly constructed compact complex line,
including real elements and zero. -/
theorem exists_octComplexLine (x : Octonion) :
    ∃ I : Octonion, octRe I = 0 ∧ octNormSq I = 1 ∧
      ∃ z : ℂ, 0 ≤ z.im ∧ octComplexLine I z = x := by
  let b := x - octScalar (octRe x)
  have hb : octRe b = 0 := by simp [b, octRe, octScalar]
  by_cases hz : b = 0
  · refine ⟨octI, rfl, ?_, ⟨octRe x,0⟩, le_rfl, ?_⟩
    · norm_num [octI, quatI, octNormSq, Quaternion.normSq_def']
    · have hx : x = octScalar (octRe x) := sub_eq_zero.mp hz
      simpa [octComplexLine, octScalar_smul] using hx.symm
  · obtain ⟨I, r, hr, hn, hdecomp⟩ := octUnit_decomposition b hz
    have hi : octRe I = 0 := by
      have h := congrArg octRe hdecomp
      rw [hb, octRe_smul] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hr.ne'
    refine ⟨I, hi, hn, ⟨octRe x,r⟩, hr.le, ?_⟩
    change (octRe x) • octScalar 1 + r • I = x
    rw [octScalar_smul, mul_one]
    rw [← hdecomp]
    dsimp [b]
    abel

/-- A unit cube root in the same genuine complex line, with the exact
unit-stabilizer cancellation required by triality normalization. -/
theorem octUnit_normalizing_cube (r : Octonion) (hr : octNormSq r = 1) :
    ∃ a : Octonion, octNormSq a = 1 ∧
      octMul a (octMul a a) = octConj r ∧
      octMul a (octMul r (octMul a a)) = octScalar 1 := by
  obtain ⟨I, hi, hn, z, -, hz⟩ := exists_octComplexLine r
  have hzn : Complex.normSq z = 1 := by
    rw [← octComplexLine_normSq I hi hn z, hz, hr]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (star z) (n := 3) (by decide)
  have hwc : w^3 = (starRingEnd ℂ) z := hw
  have hwn : Complex.normSq w = 1 := by
    apply (pow_left_inj₀ (Complex.normSq_nonneg w) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    rw [one_pow, ← map_pow, hwc, Complex.normSq_conj, hzn]
  have hc : w*(z*(w*w)) = 1 := by
    rw [show w*(z*(w*w)) = z*w^3 by ring, hwc, Complex.mul_conj, hzn, Complex.ofReal_one]
  refine ⟨octComplexLine I w, (octComplexLine_normSq I hi hn w).trans hwn, ?_, ?_⟩
  · simp only [← octComplexLine_mul I hi hn, show w*(w*w) = w^3 by ring,
      hw, ← octComplexLine_conj I hi, hz]
  · simp only [← hz, ← octComplexLine_mul I hi hn, hc, octComplexLine_one]

end
end Glennie
