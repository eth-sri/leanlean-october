module

public import RequestProject.LocalConformalWeakModes

/-!
# Compactness of the actual normalized Neumann principal remainder

The nonzero weak mode equations give a factorization through one Sobolev
derivative. The constant Fourier coefficient is retained by the genuine
rank-one projection. All operators below use the supplied physical conformal
coordinates and the actual Neumann resolvent.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The bounded symbol `(1 + |n|) / |n|`, with its zero mode removed. -/
def normalizedInverseAbsSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0 else ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)

theorem normalizedInverseAbsSymbol_pos m :
    normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simp only [normalizedInverseAbsSymbol, if_neg (show ((m + 1 : ℕ) : ℤ) ≠ 0 by omega), show sobWeight (m + 1 : ℕ) = (m + 2 : ℕ) by
    simp only [sobWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring, Int.cast_natCast,
    abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]

theorem normalizedInverseAbsSymbol_neg m :
    normalizedInverseAbsSymbol (-((m + 1 : ℕ) : ℤ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simp only [normalizedInverseAbsSymbol, if_neg (show -((m + 1 : ℕ) : ℤ) ≠ 0 by omega), show sobWeight (-(m + 1 : ℕ)) = (m + 2 : ℕ) by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring, Int.cast_neg,
    Int.cast_natCast, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]

private theorem norm_successor_ratio_le_two m :
    ‖(((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ))‖ ≤ 2 := by
  have hk : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Complex.norm_of_nonneg (div_nonneg (by positivity) hk.le), div_le_iff₀ hk]
  push_cast
  linarith

theorem norm_normalizedInverseAbsSymbol_le n :
    ‖normalizedInverseAbsSymbol n‖ ≤ 2 := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => norm_num [normalizedInverseAbsSymbol]
      | succ m =>
          change ‖normalizedInverseAbsSymbol (m + 1 : ℕ)‖ ≤ 2
          rw [normalizedInverseAbsSymbol_pos]
          exact norm_successor_ratio_le_two m
  | negSucc m =>
      rw [show Int.negSucc m = -(m + 1 : ℕ) by omega, normalizedInverseAbsSymbol_neg]
      exact norm_successor_ratio_le_two m

/-- The bounded diagonal operator for the inverse absolute frequency symbol. -/
def normalizedInverseAbsOperator : L2Z →L[ℂ] L2Z :=
  diagOp normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

@[simp] theorem normalizedInverseAbsOperator_apply b n :
    normalizedInverseAbsOperator b n = normalizedInverseAbsSymbol n * b n :=
  diagOp_apply normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le b n

/-- The rank-one projection onto the constant Fourier coefficient. -/
def zeroModeProjection : L2Z →L[ℂ] L2Z :=
  diagOp (fun n : ℤ => if n = 0 then 1 else 0) 1
    (fun n => by
      split_ifs <;> simp)

@[simp] theorem zeroModeProjection_apply b n :
    zeroModeProjection b n = (if n = 0 then 1 else 0) * b n :=
  diagOp_apply _ _ _ b n

theorem zeroModeProjection_eq_single b :
    zeroModeProjection b = lp.single 2 0 (b 0) := by
  apply lp.ext
  funext n
  rw [zeroModeProjection_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

theorem isCompactOperator_zeroModeProjection : IsCompactOperator zeroModeProjection := by
  unfold zeroModeProjection
  apply isCompactOperator_diagOp_of_finite _ _ _ ({0})
  intro n hn
  simp at hn
  simp [hn]


end PolyaNeumann

end
