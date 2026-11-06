module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The bounded symbol `(1 + |n|) / |n|`, with its zero mode removed. -/
def normalizedInverseAbsSymbol n  :=
  if n = 0 then 0 else ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)

theorem normalizedInverseAbsSymbol_pos m :
    normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight,  Int.cast_natCast,  Nat.abs_cast]
    push_cast
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn, hweight, Int.cast_natCast,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

theorem normalizedInverseAbsSymbol_neg m :
    normalizedInverseAbsSymbol (-((m + 1 : ℕ) : ℤ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simpa only [normalizedInverseAbsSymbol, neg_eq_zero, sobWeight, Int.cast_neg, abs_neg]
    using normalizedInverseAbsSymbol_pos m

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
          grind only [normalizedInverseAbsSymbol, normalizedInverseAbsSymbol_pos, norm_successor_ratio_le_two]
  | negSucc m =>
      grind only [normalizedInverseAbsSymbol_neg, norm_successor_ratio_le_two]

/-- The bounded diagonal operator for the inverse absolute frequency symbol. -/
def normalizedInverseAbsOperator  :=
  diagOp normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

@[simp] theorem normalizedInverseAbsOperator_apply b n :
    normalizedInverseAbsOperator b n = normalizedInverseAbsSymbol n * b n :=
  diagOp_apply normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le b n

/-- The rank-one projection onto the constant Fourier coefficient. -/
def zeroModeProjection : L2Z →L[ℂ] L2Z :=
  diagOp (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) 1
    (fun n => by
      aesop)

@[simp] theorem zeroModeProjection_apply b n :
    zeroModeProjection b n = (if n = 0 then 1 else 0) * b n :=
  diagOp_apply _ _ _ b n

theorem zeroModeProjection_eq_single b :
    zeroModeProjection b = lp.single 2 0 (b 0) := by
  aesop

theorem isCompactOperator_zeroModeProjection : IsCompactOperator zeroModeProjection := by
  apply isCompactOperator_diagOp_of_finite _ _ _ ({0})
  simp_all


end PolyaNeumann

end
