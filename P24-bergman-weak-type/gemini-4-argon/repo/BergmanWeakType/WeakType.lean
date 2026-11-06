/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions

/-! # Comparison and test functions for weak type constants -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

variable {μ : Measure ℂ} {T S : (ℂ → ℂ) → ℂ → ℝ≥0∞} {C D : ℝ≥0∞}

/-- Pointwise domination transfers a weak type estimate. -/
theorem isWeakTypeBound_mono (h : ∀ f, Integrable f μ → ∀ z, T f z ≤ S f z)
    (hS : IsWeakTypeBound μ S C) : IsWeakTypeBound μ T C := by
  intro f hf t ht
  apply le_trans (mul_le_mul_right (measure_mono ?_) _) (hS f hf t ht)
  exact fun z hz ↦ hz.trans_le (h f hf z)

/-- Every valid bound bounds the optimal constant from above. -/
theorem weakTypeConstant_le_of_bound (hC : IsWeakTypeBound μ T C) :
    weakTypeConstant μ T ≤ C := sInf_le hC

/-- Pointwise domination orders the optimal weak type constants. -/
theorem weakTypeConstant_mono (h : ∀ f, Integrable f μ → ∀ z, T f z ≤ S f z) :
    weakTypeConstant μ T ≤ weakTypeConstant μ S := by
  apply le_sInf
  intro C hC
  exact weakTypeConstant_le_of_bound (isWeakTypeBound_mono h hC)

end BergmanWeakType
