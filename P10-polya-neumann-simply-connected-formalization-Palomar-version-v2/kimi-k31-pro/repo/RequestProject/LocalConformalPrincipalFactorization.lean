module

public import RequestProject.LocalConformalPrincipalModes

/-!
# Compactness of the actual normalized Neumann principal remainder

The nonzero weak mode equations give a factorization through one Sobolev
derivative. The constant Fourier coefficient is retained by the genuine
rank-one projection. All operators below use the supplied physical conformal
coordinates and the actual Neumann resolvent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The bounded symbol `(1 + |n|) / |n|`, with its zero mode removed. -/
def normalizedInverseAbsSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0 else ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)

theorem normalizedInverseAbsSymbol_pos (m : ℕ) :
    normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn, hweight, Int.cast_natCast,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

theorem normalizedInverseAbsSymbol_neg (m : ℕ) :
    normalizedInverseAbsSymbol (-((m + 1 : ℕ) : ℤ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : -((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn, hweight, Int.cast_neg,
    Int.cast_natCast, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

private theorem norm_successor_ratio_le_two (m : ℕ) :
    ‖(((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ))‖ ≤ 2 := by
  have hk : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Complex.norm_of_nonneg (div_nonneg (by positivity) hk.le), div_le_iff₀ hk]
  push_cast
  linarith

theorem norm_normalizedInverseAbsSymbol_le (n : ℤ) :
    ‖normalizedInverseAbsSymbol n‖ ≤ 2 := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => norm_num [normalizedInverseAbsSymbol]
      | succ m =>
          change ‖normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ)‖ ≤ 2
          rw [normalizedInverseAbsSymbol_pos]
          exact norm_successor_ratio_le_two m
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hi, normalizedInverseAbsSymbol_neg]
      exact norm_successor_ratio_le_two m

/-- The bounded diagonal operator for the inverse absolute frequency symbol. -/
def normalizedInverseAbsOperator : L2Z →L[ℂ] L2Z :=
  diagOp normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

@[simp] theorem normalizedInverseAbsOperator_apply (b : L2Z) (n : ℤ) :
    normalizedInverseAbsOperator b n = normalizedInverseAbsSymbol n * b n :=
  diagOp_apply normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le b n

/-- The rank-one projection onto the constant Fourier coefficient. -/
def zeroModeProjection : L2Z →L[ℂ] L2Z :=
  diagOp (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) 1
    (fun n => by
      change ‖(if n = 0 then (1 : ℂ) else 0)‖ ≤ 1
      split_ifs <;> simp)

@[simp] theorem zeroModeProjection_apply (b : L2Z) (n : ℤ) :
    zeroModeProjection b n = (if n = 0 then 1 else 0) * b n :=
  diagOp_apply _ _ _ b n

theorem zeroModeProjection_eq_single (b : L2Z) :
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
  apply isCompactOperator_diagOp_of_finite _ _ _ ({0} : Finset ℤ)
  intro n hn
  simp at hn
  simp [hn]

section

variable {R : ℝ} (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

end

end PolyaNeumann

end
