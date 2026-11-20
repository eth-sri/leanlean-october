/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarKernel

/-! # Polar differential equations under compact source integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real Metric
open scoped Topology

namespace BergmanWeakType.Weighted

/-- A finite positive source, including sources on the boundary of the disk. -/
abbrev PolarSource := Measure ClosedDisk

namespace PolarSource
variable (s : PolarSource) [IsFiniteMeasure s] (q : ℝ)

/-- Evaluate the positive kernel on a finite source, including boundary sources. -/
def potential (α : ℝ) (z : ℂ) := ∫ w, ‖weightedKernel α z w.val‖ ∂s

@[fun_prop] theorem measurable_potential (α : ℝ) : Measurable (s.potential α) :=
  (StronglyMeasurable.integral_prod_right' (f := fun p : ℂ × ClosedDisk ↦ ‖weightedKernel α p.1 p.2.val‖) (by measurability)).measurable

def avg (i : Part) (p : ℝ × ℝ) := ∫ w, column q i p w ∂s

theorem integrable_column (i : Part) {p : ℝ × ℝ} (hp : p ∈ cylinder) : Integrable (column q i p) s := by
  apply Continuous.integrable_of_hasCompactSupport _ (.of_compactSpace _)
  apply continuousOn_univ.mp ((column_continuous q i).comp (continuous_const.prodMk continuous_id).continuousOn _)
  simp_all

/-- Continuity and all pure derivatives commute with integration over the compact source disk. -/
def field : Field where
  get p i := s.avg q i p
  cont i := (continuousOn_integral_of_compact_support (μ := s) isCompact_univ (column_continuous q i) (by simp)).mono
    fun p hp ↦ square_lt_one hp.1
  jet l x hx := integral_jet isCompact_univ (by simp) (column_continuous q) l.cont
    ((isOpen_lt ((continuous_fst.comp l.cont).pow 2) continuous_const).mem_nhds hx)
    (fun w _ u ↦ column_jet w q l u)
  period i x := by simp [avg,column_period]

theorem value (α r t : ℝ) : (s.field (-(α+2)/2)).val .v r t = s.potential α (circleMap 0 r t) := by
  simp only [Field.val,Field.eval,field,avg,column_val,potential]

private theorem error_integral (k : ℝ) {x : ℝ} (hx : x^2 < 1) (θ : ℝ) :
    (((s.field (-k/2)).eval x θ).error k x) = ∫ w, Jet.error (fun i ↦ column (-k/2) i (x,θ) w) k x ∂s := by
  have hi i := s.integrable_column (-k/2) i (p := (x,θ)) hx
  simp (disch := fun_prop) [Jet.error, rhs, field, avg, integral_sub, integral_add, integral_div, integral_const_mul]

theorem error_nonpos (k : ℝ) {x : ℝ} (hx : x^2 < 1) (hn : x ≠ 0) (θ : ℝ) :
    ((s.field (-k/2)).eval x θ).error k x ≤ 0 := by
  rw [s.error_integral k hx θ]; apply integral_nonpos; intro w; dsimp only [Pi.zero_apply]
  rw [column_equation w x θ k hx hn, neg_div, neg_mul, neg_nonpos]
  have := polarDenominator_pos w x θ hx
  have := sub_nonneg.mpr (unit_sq w)
  change 0 ≤ _ * polarDenominator w x θ ^ (-k/2); positivity

theorem error_boundary (k : ℝ) {x : ℝ} (hx : x^2 < 1) (hn : x ≠ 0) (θ : ℝ)
    (hb : ∀ᵐ w ∂s, ‖w.val‖ = 1) : ((s.field (-k/2)).eval x θ).error k x = 0 := by
  rw [s.error_integral k hx θ]; apply integral_eq_zero_of_ae
  filter_upwards [hb] with w hw; simp_all [column_equation]

end PolarSource
end BergmanWeakType.Weighted
