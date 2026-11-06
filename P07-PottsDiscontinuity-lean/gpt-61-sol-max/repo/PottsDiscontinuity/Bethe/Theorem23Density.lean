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
theorem densityNorm_pointwise_le {Δ : ℝ} (hΔ : Δ < -1) (f : ℝ → ℝ)
    (hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
    (B : ℝ) (hB : densityNorm Δ hΔ f hbounded ≤ B)
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤ B := LE.le.trans (le_csSup hbounded (Exists.intro ⟨α, hα⟩ rfl)) hB

/-- The `Ξ` weight in (2.3) has a positive lower bound uniform over
`Δ ≤ Δ₀ < -1`. -/
theorem exists_uniform_Xi_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ α : ℝ,
      m ≤ Xi (lamOf Δ) α := by
  let lam₀ := lamOf Δ₀
  
  have hlam₀  := lamOf_pos hΔ₀
  have hexp : 1 < Real.exp lam₀ := by simpa using hlam₀
  
  refine ⟨ (Real.exp lam₀ - 1) / (Real.exp lam₀ + 1) ,  by
                positivity , fun Δ hΔ α => ?_⟩
  
  
  
  
  exact (exp_ratio_mono' hlam₀ (lamOf_mono hΔ₀ hΔ)).trans (Xi_ge_exp_ratio (lamOf_pos (lt_of_le_of_lt hΔ hΔ₀)) α)

section

variable {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) (f : ℝ → ℝ) (hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|)) (B m : ℝ) (hm : 0 < m) (hXi : ∀ α : ℝ, m ≤ Xi (lamOf Δ) α) (hB : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀) f hbounded ≤ B)
include hm hXi hB

/-- A weighted supremum bound controls the unweighted error because `Ξ` is
uniformly bounded below. -/
theorem densityNorm_unweighted_pointwise_le 
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |f (kMap (lamOf Δ) α)| ≤ B / m := by
  have hXiα := hXi α
  
  have hweighted := densityNorm_pointwise_le (lt_of_le_of_lt hΔ hΔ₀) f
    hbounded B hB hα
  rw [abs_mul, abs_of_pos (lt_of_lt_of_le hm hXiα)] at hweighted
  
  exact (le_div_iff₀ hm).2 (by simpa [mul_comm] using  (mul_le_mul_of_nonneg_right hXiα (abs_nonneg _)).trans hweighted )

/-- The weighted norm bound also controls the unweighted density error at each
physical coordinate `x ∈ [-π, π]`. -/
theorem densityNorm_x_pointwise_le 
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |f x| ≤ B / m := by
  have hlam  := lamOf_pos (lt_of_le_of_lt hΔ hΔ₀)
  
  
  simpa only [kMap_kInv hlam] using  densityNorm_unweighted_pointwise_le hΔ₀ hΔ f hbounded B m hm hXi hB (kInv_mem_Icc hlam hx) 

end

  
  

end PottsDiscontinuity.Bethe
