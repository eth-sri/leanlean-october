module

public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.QldEnvelope

/-! # Absorption of the actual rounded polynomial-pair error

The direct passing envelope, low-degree soundness, and projective rounding
are composed in the same polynomial error domain.
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- Universal absorption of the actual rounded pair error from `lem:qld-4-7`. -/
theorem exists_actual_rounded_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (a b : ℝ)
    (ha : 1 ≤ a) (hb : 0 < b) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        P.pairError (pointError epsilon)
          (P.extendedLdError a b (pointError epsilon) (P.m * lineError epsilon P.degreeRatio)) ≤
          P.qldError A B epsilon := by
  let extended (w : QldInput) : ℝ := ((2 * w.1.m + 2) * w.1.d : ℕ)
  have hp := QldInput.polynomial_error.compose hpoint
  have hr := QldInput.polynomial_ratio
  have hml := (QldInput.polynomial_error.compose₂ hr hline).mul_growth zero_le_one zero_le_one
    (g := fun w => (w.1.m : ℝ)) fun w => by
      refine ⟨by positivity, ?_⟩
      rw [Real.rpow_one, one_mul]
      change (w.1.m : ℝ) ≤ w.1.degreeBudget
      exact_mod_cast Nat.le_mul_of_pos_right w.1.m w.1.hd
  have hpass := (((hp.add hml).sqrt).add hr).scale (C := 3) (by norm_num)
  have hsize (w : QldInput) : w.1.degreeBudget ≤ extended w ∧ extended w ≤ 4 * w.1.degreeBudget := by
    have hm : (1 : ℝ) ≤ w.1.m := by exact_mod_cast w.1.one_le_m
    dsimp [extended]
    push_cast
    rw [← mul_assoc]
    constructor <;> gcongr <;> linarith
  let δ (w : QldInput) := w.1.extendedLdError a b (pointError w.error)
    (w.1.m * lineError w.error w.1.degreeRatio)
  have hLd : QldInput.domain.Polynomial δ := by
    simpa only [δ, AdmissibleParams.extendedLdError, deltaLd, Nat.mul_one,
      Nat.mul_comm _ (2 * _ + 2), directPassingErrorEnvelope, extended, Real.rpow_eq_pow] using
      QldInput.polynomial_soundness hpass extended (by norm_num) (zero_le_one.trans ha) hb hsize
  have h : QldInput.domain.Polynomial (fun w =>
      32 * roundedLdError (δ w) + 64 * pointError w.error + 30 * w.1.degreeRatio) := by
    unfold roundedLdError
    apply_rules [ErrorDomain.Polynomial.add, ErrorDomain.Polynomial.scale,
      ErrorDomain.Polynomial.sqrt, ErrorDomain.Polynomial.rpow, hLd, hp, hr] <;> norm_num
  obtain ⟨A, B, hA, hB, hB1, hfinal⟩ := QldInput.exists_qldEnvelope h
  refine ⟨A, B, hA, hB, hB1, fun P epsilon he he1 => ?_⟩
  let w : QldInput := (P, ⟨epsilon, he, he1⟩)
  have hratio : (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤ 30 * P.degreeRatio := by
    have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
    have hd : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    unfold AdmissibleParams.degreeRatio
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast
    nlinarith
  refine (le_trans ?_ (hfinal w))
  dsimp only [AdmissibleParams.pairError, w, QldInput.error]
  linarith only [hratio]

end MIPStarRE.QPBT
