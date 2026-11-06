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
    (P : Measure Ω) U (dens : ℂ → ℝ) ε₀
    Y
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    K (hK : IsCompact K) (hKU : K ⊆ U) :
    logRegularizationReference U dens K ≠ ∞ := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hY.densityContinuous.mono hKU)
  let B₀ := max B 0
  have hKmeas := hK.isClosed.measurableSet
  rw [logRegularizationReference, withDensity_apply _ hKmeas]
  apply ne_of_lt
  calc
    (∫⁻ x in K, ENNReal.ofReal (dens x) ∂volume.restrict U) ≤
        ∫⁻ x in K, ENNReal.ofReal B₀ ∂volume.restrict U := by
          exact setLIntegral_mono' (s := K)
            (f := fun x => ENNReal.ofReal (dens x))
            (g := fun _ : ℂ => ENNReal.ofReal B₀)
            hKmeas
            (fun x hx => (show ∀ x ∈ K, ENNReal.ofReal (dens x) ≤ ENNReal.ofReal B₀ by intro x hx; exact ENNReal.ofReal_le_ofReal (by dsimp [B₀]; exact le_trans (hB (Set.mem_image_of_mem dens hx)) (le_max_left _ _))) x hx)
    _ = ENNReal.ofReal B₀ * (volume.restrict U) K := by
          rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal B₀ * volume K := by
          gcongr
          exact Measure.restrict_le_self
    _ < ∞ := by
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top


end DOZZ.Proofs
