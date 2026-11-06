module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! # Measurable countable-valued upper time approximations -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Filter MeasureTheory
open scoped Topology

/-- The integer index of the upper mesh approximation of a terminal time. -/
def terminalTimeMeshIndex (j : ℕ) (τ : ℝ) : ℤ := Int.ceil (τ * ((j : ℝ) + 1))

/-- The upper mesh approximation, with mesh size `1 / (j + 1)`. -/
def terminalTimeMesh (j : ℕ) (τ : ℝ) : ℝ :=
  (terminalTimeMeshIndex j τ : ℝ) / ((j : ℝ) + 1)

variable (j : ℕ) (τ : ℝ)

/-- The mesh index is Borel measurable. -/
theorem measurable_terminalTimeMeshIndex  : Measurable (terminalTimeMeshIndex j) :=
  Int.measurable_ceil.comp (measurable_id.mul_const _)

/-- Every upper mesh approximation is at least the original time. -/
theorem le_terminalTimeMesh  : τ ≤ terminalTimeMesh j τ := by
  rw [terminalTimeMesh, le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- The upper mesh error is at most the mesh size. -/
theorem terminalTimeMesh_sub_le  :
    terminalTimeMesh j τ - τ ≤ 1 / ((j : ℝ) + 1) := by
  have hh := Int.ceil_lt_add_one (τ * (j + 1))
  dsimp only [terminalTimeMesh, terminalTimeMeshIndex]
  field_simp
  linarith

/-- Upper mesh times tend to their original terminal time. -/
theorem tendsto_terminalTimeMesh  :
    Tendsto (fun j => terminalTimeMesh j τ) atTop (𝓝 τ) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm (j : ℕ) : ‖terminalTimeMesh j τ - τ‖ = terminalTimeMesh j τ - τ :=
    Real.norm_of_nonneg (sub_nonneg.mpr (le_terminalTimeMesh j τ))
  simp only [hnorm]
  exact squeeze_zero (fun j => sub_nonneg.mpr (le_terminalTimeMesh j τ))
    (fun j => terminalTimeMesh_sub_le j τ) tendsto_one_div_add_atTop_nhds_zero_nat

end HypoellipticAleksandrov.KineticAleksandrov
