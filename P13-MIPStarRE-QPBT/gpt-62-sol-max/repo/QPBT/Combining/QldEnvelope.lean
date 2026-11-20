module

public import QPBT.Combining.PowerEnvelope
public import QPBT.Combining.RoundedError

/-! Polynomial decay in the Pauli test's noise and field-size tails. -/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

abbrev QldInput := AdmissibleParams × Set.Icc (0 : ℝ) 1

namespace QldInput

abbrev error (w : QldInput) : ℝ := w.2.val
abbrev inverseField (w : QldInput) : ℝ := (w.1.q : ℝ) ^ (-1 : ℝ)
abbrev exponentialTail (w : QldInput) : ℝ := (2 : ℝ) ^ (-w.1.degreeBudget)

/-- Use the degree budget as size and the largest of the three tails as noise. -/
def domain : ErrorDomain QldInput where
  size w := w.1.degreeBudget
  noise w := max w.error (max w.inverseField w.exponentialTail)
  size_ge_one w := w.1.degreeBudget_ge_one
  noise_nonneg w := w.2.2.1.trans (le_max_left ..)
  noise_le_one w := max_le w.2.2.2 (max_le
    (Real.rpow_le_one_of_one_le_of_nonpos w.1.fieldSize_ge_one (by norm_num))
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (zero_le_one.trans w.1.degreeBudget_ge_one))))

theorem polynomial_error : domain.Polynomial error :=
  domain.polynomial_noise.mono fun w => ⟨w.2.2.1, le_max_left ..⟩

private theorem polynomial_inverseField : domain.Polynomial inverseField :=
  domain.polynomial_noise.mono fun _ => ⟨by positivity, (le_max_left ..).trans (le_max_right ..)⟩

theorem polynomial_ratio : domain.Polynomial (fun w => w.1.degreeRatio) := by
  simpa only [AdmissibleParams.degreeRatio, inverseField, domain, Real.rpow_neg_one, div_eq_mul_inv]
    using polynomial_inverseField.mul_size

/-- The low-degree error formula is polynomially bounded if its effective degree
lies between the original budget and a constant times that budget. -/
theorem polynomial_soundness {err : QldInput → ℝ} (he : domain.Polynomial err)
    (size : QldInput → ℝ) {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 < b)
    (hs : ∀ w, w.1.degreeBudget ≤ size w ∧ size w ≤ C * w.1.degreeBudget) :
    domain.Polynomial (fun w =>
      a * size w ^ a * (err w ^ b + (w.1.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * size w)))) := by
  have hq : domain.Polynomial (fun w => (w.1.q : ℝ) ^ (-b)) := by
    simpa only [inverseField, ← Real.rpow_mul (Nat.cast_nonneg _), neg_one_mul]
      using polynomial_inverseField.rpow hb
  have hx : domain.Polynomial exponentialTail := domain.polynomial_noise.mono fun _ =>
    ⟨by positivity, (le_max_right ..).trans (le_max_right ..)⟩
  have ht : domain.Polynomial (fun w => (2 : ℝ) ^ (-(b * size w))) := by
    refine (hx.rpow hb).mono fun w => ⟨by positivity, ?_⟩
    simp only [exponentialTail, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul,
      mul_comm w.1.degreeBudget b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (by gcongr; exact (hs w).1))
  refine (((he.rpow hb).add hq).add ht).mul_growth (C := a * C ^ a) (by positivity) ha fun w => ?_
  have h₀ := zero_le_one.trans (w.1.degreeBudget_ge_one.trans (hs w).1)
  refine ⟨by positivity, ?_⟩
  change a * size w ^ a ≤ a * C ^ a * w.1.degreeBudget ^ a
  rw [mul_assoc, ← Real.mul_rpow hC (zero_le_one.trans w.1.degreeBudget_ge_one)]
  gcongr
  exact (hs w).2

/-- Turn the polynomial envelope into the registered soundness error. -/
theorem exists_qldEnvelope {f : QldInput → ℝ} (h : domain.Polynomial f) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧ ∀ w : QldInput, f w ≤ w.1.qldError A B w.error := by
  obtain ⟨A, B, hA, hB, hB1, hf⟩ := h.exists_envelope
  refine ⟨A, B, hA, hB, hB1, fun w => (hf w).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by dsimp [domain]; positivity)
  have he := w.2.2.1
  change (max w.error (max w.inverseField w.exponentialTail)) ^ B ≤ w.1.qldTail B w.error
  rw [Real.rpow_max he (le_max_of_le_left (by positivity)) hB.le,
    Real.rpow_max (by positivity) (by positivity) hB.le]
  simp only [inverseField, exponentialTail, ← Real.rpow_mul (Nat.cast_nonneg w.1.q),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul, one_mul,
    mul_comm w.1.degreeBudget B, max_le_iff, AdmissibleParams.qldTail]
  have h1 := Real.rpow_nonneg he B
  have h2 := Real.rpow_nonneg (Nat.cast_nonneg w.1.q) (-B)
  have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(B * w.1.degreeBudget))
  and_intros <;> linarith

end QldInput

end

end MIPStarRE.QPBT
