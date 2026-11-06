/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization

/-! Local finiteness of the reference measure of an admissible logarithmic regularization. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The deterministic reference measure of an admissible logarithmic regularization is finite on
every compact subset of its chart. -/
theorem admissible_logRegularization_reference_measure_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    logRegularizationReference U dens K ≠ ∞ := by
  have hcont := hY.densityContinuous.mono hKU
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont
  let B₀ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right ..
  have hpoint : ∀ x ∈ K, ENNReal.ofReal (dens x) ≤ ENNReal.ofReal B₀ := by
    intro x hx
    have hle : dens x ≤ B₀ := by
      aesop
    simp_all
  have hKmeas := hK.isClosed.measurableSet
  rw [logRegularizationReference, withDensity_apply _ hKmeas]
  apply ne_of_lt
  calc
    (∫⁻ x in K, ENNReal.ofReal (dens x) ∂volume.restrict U) ≤
        ∫⁻ x in K, ENNReal.ofReal B₀ ∂volume.restrict U := setLIntegral_mono'
           
           
            hKmeas
            (fun x hx => hpoint x hx)
    _ = ENNReal.ofReal B₀ * (volume.restrict U) K := by
          simp
    _ ≤ ENNReal.ofReal B₀ * volume K := by
          gcongr
          exact Measure.restrict_le_self
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top


end DOZZ.Proofs
