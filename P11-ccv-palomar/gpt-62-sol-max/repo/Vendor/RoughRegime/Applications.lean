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

section
variable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f)
include hf

lemma square_tail_lower (t : ℝ) (ht : 0 ≤ t) :
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
  simp_all

lemma eLpNorm_two_eq_squaredIntegral :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simp_all [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

end

end RoughRegime.Applications
