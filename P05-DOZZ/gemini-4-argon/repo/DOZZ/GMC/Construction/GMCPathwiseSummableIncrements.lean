/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Summable expected successive increments give an almost-sure cutoff limit. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs


/-- A summable expected-increment bound over countably many observables gives one common
full-measure set on which every observable's cutoff sequence converges. -/
theorem ae_forall_tendsto_of_summable_lintegral_abs_increments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (hF : ∀ i n, Measurable (F i n))
    (hsum : ∀ i, (∑' n, ∫⁻ ω,
      ENNReal.ofReal |F i n.succ ω - F i n ω| ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ i, ∃ L : ℝ, Tendsto (fun n => F i n ω) atTop (𝓝 L) := by
  have ae_tendsto_of_summable_lintegral_abs_increments (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) (hsum : (∑' n, ∫⁻ ω, ENNReal.ofReal |F n.succ ω - F n ω| ∂P) ≠ ∞) : ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun n => F n ω) atTop (𝓝 L) := by
    let Q : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal |F n.succ ω - F n ω|
    have hQ n : Measurable (Q n) := ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp ((hF n.succ).sub (hF n)))
    filter_upwards [(ae_lt_top' (AEMeasurable.tsum fun n => (hQ n).aemeasurable) (by rw [lintegral_tsum (fun n => (hQ n).aemeasurable)]; simpa only [Q] using hsum))] with ω hω
    have hCauchy : CauchySeq (fun n => F n ω) := by
      apply cauchySeq_of_edist_le_of_tsum_ne_top (fun n => Q n ω)
      · intro n
        dsimp [Q]
        rw [edist_dist, Real.dist_eq]
        exact le_of_eq (by rw [abs_sub_comm])
      · exact hω.ne
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
    exact ⟨L, hL⟩
  apply ae_all_iff.mpr
  intro i
  apply ae_tendsto_of_summable_lintegral_abs_increments (fun n => F i n)
    (fun n => hF i n)
  exact hsum i

end DOZZ.Proofs
