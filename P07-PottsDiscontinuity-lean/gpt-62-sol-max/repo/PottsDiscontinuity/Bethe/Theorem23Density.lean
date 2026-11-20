module

public import Mathlib
public import PottsDiscontinuity.Bethe.AsymptoticDefs
public import PottsDiscontinuity.Bethe.Prop21Positivity

/-!
# Basic consequences of the Bethe density norm

This module reuses the definitions of (2.3) and (2.5) from
`AsymptoticDefs.lean`.  In particular, norm bounds are always interpreted on
the full closed parameter interval used in (2.3).
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- A bound on `densityNorm` bounds its weighted integrand at every point of
`[-π, π]`. -/
theorem densityNorm_pointwise_le {Δ : ℝ} (f : ℝ → ℝ)
    (hbounded : BddAbove (densityValues Δ f))
    (B : ℝ) (hB : densityNorm Δ f ≤ B)
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤ B := by
  have hpoint : |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤
      densityNorm Δ f := by
    apply le_csSup hbounded
    tauto
  exact hpoint.trans hB

/-- The `Ξ` weight in (2.3) has a positive lower bound uniform over
`Δ ≤ Δ₀ < -1`. -/
theorem exists_uniform_Xi_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ α : ℝ,
      m ≤ Xi (lamOf Δ) α := by
  obtain ⟨X, hX, hXi⟩ := exists_Xi_uniform_bounds (lamOf_pos hΔ₀)
  exact ⟨X⁻¹, inv_pos.2 (zero_lt_one.trans hX), fun Δ hΔ α => (hXi _ (lamOf_mono hΔ₀ hΔ) α).1⟩

/-- The weighted norm bound also controls the unweighted density error at each
physical coordinate `x ∈ [-π, π]`. -/
theorem densityNorm_x_pointwise_le {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) (f : ℝ → ℝ)
    (hbounded : BddAbove (densityValues Δ f))
    (B m : ℝ) (hm : 0 < m)
    (hXi : ∀ α : ℝ, m ≤ Xi (lamOf Δ) α)
    (hB : densityNorm Δ f ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |f x| ≤ B / m := by
  have hlam := lamOf_pos (hΔ.trans_lt hΔ₀)
  have h := densityNorm_pointwise_le f hbounded B hB (kInv_mem_Icc hlam hx)
  rw [kMap_kInv hlam, abs_mul, abs_of_pos (hm.trans_le (hXi _))] at h
  exact (le_div_iff₀' hm).2 ((mul_le_mul_of_nonneg_right (hXi _) (abs_nonneg _)).trans h)

theorem exists_uniform_Xi_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ X : ℝ, 0 < X ∧ ∀ Δ ≤ Δ₀, ∀ α : ℝ, Xi (lamOf Δ) α ≤ X := by
  obtain ⟨X, hX, hXi⟩ := exists_Xi_uniform_bounds (lamOf_pos hΔ₀)
  exact ⟨X, zero_lt_one.trans hX, fun Δ hΔ α => (hXi _ (lamOf_mono hΔ₀ hΔ) α).2⟩

end PottsDiscontinuity.Bethe
