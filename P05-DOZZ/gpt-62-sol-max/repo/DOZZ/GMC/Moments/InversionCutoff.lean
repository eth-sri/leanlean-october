/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionReference
public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.GMC.CircleWickDensity

/-! Exact transport of Wick cutoffs under a measure-preserving involution. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Mapping a density through a measure-preserving involution composes the density with that
involution. -/
theorem measurePreserving_involutive_map_withDensity
    {α : Type*} [MeasurableSpace α] (φ : α → α) (μ : Measure α)
    (hφ : MeasurePreserving φ μ μ) (hinv : Function.Involutive φ)
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity g).map φ = μ.withDensity (fun x => g (φ x)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hφ.measurable hs, withDensity_apply _ (hs.preimage hφ.measurable),
    withDensity_apply _ hs]
  let hrestrict := hφ.restrict_preimage hs
  calc
    (∫⁻ x in φ ⁻¹' s, g x ∂μ) =
        ∫⁻ x in φ ⁻¹' s, g (φ (φ x)) ∂μ := by
          apply setLIntegral_congr_fun (hs.preimage hφ.measurable)
          intro x hx
          exact (congrArg g (hinv x)).symm
    _ = ∫⁻ x in s, g (φ x) ∂μ := hrestrict.lintegral_comp (hg.comp hφ.measurable)

/-- The regularized equator chaos is the compactifying reference measure multiplied by its Wick
factor. -/
theorem regularizedGMC_eq_reference_withDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω)
    (hwick : Measurable (gmcCircleWickDensity P Xc γ r ω)) :
    regularizedGMC P Xc γ r ω = gmcReferenceMeasure.withDensity (gmcCircleWickDensity P Xc γ r ω) := by
  change _ = (volume.withDensity refWeight).withDensity _
  rw [← withDensity_mul _ refWeight_measurable hwick, regularizedGMC]
  congr 1
  funext x
  simp only [Pi.mul_apply, refWeight, gmcCircleWickDensity, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact mul_comm _ _

/-- The finite-cutoff chaos after complex inversion is exactly the cutoff chaos formed from the
inverted circle-average profile. The field input is abstract here; the pulled-circle covariance
and admissibility estimates are separate. -/
theorem regularizedGMC_map_complexInv
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω)
    (hwick : Measurable (gmcCircleWickDensity P Xc γ r ω)) :
    (regularizedGMC P Xc γ r ω).map (fun x : ℂ => x⁻¹) =
      regularizedGMC P (fun ω y s => Xc ω y⁻¹ s) γ r ω := by
  let φ : ℂ → ℂ := fun x => x⁻¹
  have hmeas : Measurable φ := by fun_prop
  have hinv : Function.Involutive φ := by
    intro x
    simp [φ]
  have hp : MeasurePreserving φ gmcReferenceMeasure gmcReferenceMeasure :=
    ⟨hmeas, by simpa [φ] using gmcReferenceMeasure_map_complexInv⟩
  let w := gmcCircleWickDensity P Xc γ r ω
  have hwickInv : Measurable (gmcCircleWickDensity P (fun ω y s => Xc ω y⁻¹ s) γ r ω) :=
    hwick.comp hmeas
  rw [regularizedGMC_eq_reference_withDensity P Xc γ r ω hwick,
    regularizedGMC_eq_reference_withDensity P (fun ω y s => Xc ω y⁻¹ s) γ r ω hwickInv,
    measurePreserving_involutive_map_withDensity φ gmcReferenceMeasure hp hinv w hwick]
  rfl

end DOZZ.Proofs
