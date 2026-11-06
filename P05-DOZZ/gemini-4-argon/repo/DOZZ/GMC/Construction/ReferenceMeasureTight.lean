/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Compact cutoffs exhaust the finite equator GMC reference measure. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DOZZ.Proofs

/-- The reference mass outside growing closed disks tends to zero. -/
theorem gmcReferenceMeasure_compl_closedBall_tendsto_zero :
    Tendsto (fun n : ℕ => gmcReferenceMeasure (Metric.closedBall (0 : ℂ) n)ᶜ)
      atTop (𝓝 0) := by
  let S : ℕ → Set ℂ := fun n => (Metric.closedBall (0 : ℂ) n)ᶜ
  have hanti : Antitone S := by
    intro n m hnm x hx
    intro hxclosed
    apply hx
    apply Metric.mem_closedBall.mpr
    exact (show dist x (0 : ℂ) ≤ (n : ℝ) by simpa [Metric.mem_closedBall] using hxclosed).trans (by exact_mod_cast hnm)
  have hempty : (⋂ n, S n) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact False.elim ((Set.mem_iInter.mp hx n) (by apply Metric.mem_closedBall.mpr; simpa [dist_zero_right] using hn.le))
    · intro hx
      exact False.elim (Set.notMem_empty x hx)
  have hfinite : ∃ n, gmcReferenceMeasure (S n) ≠ ∞ := by
    refine ⟨0, ?_⟩
    apply ne_of_lt
    exact (measure_mono (Set.subset_univ _)).trans_lt
      (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)
  simpa [Function.comp_def, S, hempty] using (tendsto_measure_iInter_atTop (fun n => by exact ((Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (n : ℝ))).measurableSet.compl).nullMeasurableSet) hanti hfinite)

end DOZZ.Proofs
