/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Approximation by sequences converging in measure. -/
@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace DOZZ.Proofs

/-- Arbitrarily accurate probability approximations transfer convergence in measure. -/
theorem tendstoInMeasure_of_probApprox {Ω ι E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    {P : Measure Ω} {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (h : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ → ∃ (a : ι → Ω → E) (b : Ω → E),
      TendstoInMeasure P a l b ∧ (∀ᶠ i in l, P {ω | ε ≤ dist (f i ω) (a i ω)} ≤ δ) ∧
        P {ω | ε ≤ dist (b ω) (g ω)} ≤ δ) : TendstoInMeasure P f l g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let t := ε / 3
  let d := δ / 3
  have ht : 0 < t := by dsimp [t]; positivity
  have hd : 0 < d := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨a, b, hab, ha, hb⟩ := h t ht d hd
  filter_upwards [ha, ENNReal.tendsto_nhds_zero.mp (tendstoInMeasure_iff_dist.mp hab t ht) d hd]
    with i hi hj
  let A := {ω | t ≤ dist (f i ω) (a i ω)}
  let B := {ω | t ≤ dist (a i ω) (b ω)}
  let C := {ω | t ≤ dist (b ω) (g ω)}
  have hs : {ω | ε ≤ dist (f i ω) (g ω)} ⊆ A ∪ B ∪ C := by
    intro ω hω
    by_contra hnot
    simp only [A, B, C, mem_union, mem_setOf_eq, not_or, not_le] at hnot
    have := dist_triangle4 (f i ω) (a i ω) (b ω) (g ω)
    change ε ≤ dist (f i ω) (g ω) at hω
    rcases hnot with ⟨⟨h₁, h₂⟩, h₃⟩
    dsimp [t] at h₁ h₂ h₃
    linarith
  calc
    _ ≤ P (A ∪ B ∪ C) := measure_mono hs
    _ ≤ P A + P B + P C := (measure_union_le ..).trans (add_le_add (measure_union_le ..) le_rfl)
    _ ≤ d + d + d := add_le_add (add_le_add hi hj) hb
    _ = δ := by
      rw [← two_mul, ← add_one_mul, show (2 : ℝ≥0∞) + 1 = 3 by norm_num]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end DOZZ.Proofs
