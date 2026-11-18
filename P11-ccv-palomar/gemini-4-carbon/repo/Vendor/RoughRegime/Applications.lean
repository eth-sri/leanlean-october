module

public import Mathlib

@[expose] public section

/-!
# Embedding and application reductions

This file proves the finite score embedding, Lemma 18 (hardness to risk),
the probability-event and Chebyshev steps of Lemma 19, and explicit
algebraic constructions used in Appendices B--D. The asymptotic lower
bound and the pilot's concentration theorem are not asserted here.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace RoughRegime.Applications

/-- A measurable estimator on an arbitrary experiment, including an experiment
with an auxiliary random seed. -/
abbrev Estimator (Ω : Type*) [MeasurableSpace Ω] := {f : Ω → ℝ // Measurable f}

instance estimator_nonempty (Ω : Type*) [MeasurableSpace Ω] : Nonempty (Estimator Ω) :=
  ⟨⟨fun _ => 0, measurable_const⟩⟩

lemma square_tail_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) * μ {x | t ≤ |f x|} ≤
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  have hs : MeasurableSet {x | t ≤ |f x|} := measurableSet_le measurable_const hf.abs
  rw [← lintegral_indicator_const hs]
  apply lintegral_mono
  intro x
  by_cases hx : t ≤ |f x|
  · rw [Set.indicator_of_mem (show x ∈ {x | t ≤ |f x|} from hx)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs (f x), sq_nonneg (|f x| - t)]
  · rw [Set.indicator_of_notMem (show x ∉ {x | t ≤ |f x|} from hx)]
    exact bot_le

lemma eLpNorm_two_eq_squaredIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  congr 2
  funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

end RoughRegime.Applications
