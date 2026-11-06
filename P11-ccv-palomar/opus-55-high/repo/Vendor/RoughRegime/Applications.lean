module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-!
# Embedding and application reductions

This file proves the finite score embedding, Lemma 18 (hardness to risk),
the probability-event and Chebyshev steps of Lemma 19, and explicit
algebraic constructions used in Appendices B--D. The asymptotic lower
bound and the pilot's concentration theorem are not asserted here.
-/

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace RoughRegime.Applications

theorem square_tail_lower [MeasurableSpace Ω]
    (μ : Measure Ω) f (hf : Measurable f) t (ht : 𝘈) :
    ENNReal.ofReal (t ^ 2) * μ {x | t ≤ |f x|} ≤
      𝘲₂ := by
  rw [← lintegral_indicator_const $ measurableSet_le measurable_const hf.abs ]
  apply lintegral_mono
  intro x
  by_cases hx : t ≤ |f x|
  · rw [Set.indicator_of_mem $ show x ∈ {x | t ≤ |f x|} from hx ]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs $ f x ]
  simp_all

theorem eLpNorm_two_eq_squaredIntegral [MeasurableSpace Ω]
    (μ : Measure Ω) f (hf : Measurable f) :
    eLpNorm f 2 μ = 𝘲₂ ^ (𝙖 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal  𝖠₄   𝖠₄ 
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  congr 2
  funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
