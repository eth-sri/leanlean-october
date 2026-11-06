/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionReference
public import DOZZ.Statements.Defs.RegularizedGMC

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
  calc
    (∫⁻ x in φ ⁻¹' s, g x ∂μ) =
        ∫⁻ x in φ ⁻¹' s, g (φ (φ x)) ∂μ := by
          apply setLIntegral_congr_fun (hs.preimage hφ.measurable)
          intro x hx
          exact (congrArg g (hinv x)).symm
    _ = ∫⁻ x in s, g (φ x) ∂μ := by
          exact (hφ.restrict_preimage hs).lintegral_comp (hg.comp hφ.measurable)


/-- The finite-cutoff chaos after complex inversion is exactly the cutoff chaos formed from the
inverted circle-average profile. The field input is abstract here; the pulled-circle covariance
and admissibility estimates are separate. -/
theorem regularizedGMC_map_complexInv
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) γ r ω
    (hwick : Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))) ) :
    (regularizedGMC P Xc γ r ω).map (fun x : ℂ => x⁻¹) =
      regularizedGMC P (fun ω y s => Xc ω y⁻¹ s) γ r ω := by
  have regularizedGMC_eq_reference_withDensity (Xc : Ω → ℂ → ℝ → ℝ) γ r ω (hwick : Measurable (fun x => ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)))) : regularizedGMC P Xc γ r ω = gmcReferenceMeasure.withDensity (fun x : ℂ => ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))) := by
    apply Measure.ext
    intro s hs
    change (volume.withDensity (fun x : ℂ => ENNReal.ofReal
        (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
          normPlus x ^ (-4 : ℝ)))) s =
      (gmcReferenceMeasure.withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)))) s
    calc
      _ = ∫⁻ x in s, ENNReal.ofReal
          (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
            normPlus x ^ (-4 : ℝ)) ∂volume := withDensity_apply _ hs
      _ = ∫⁻ x in s, ENNReal.ofReal
          (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))
            ∂gmcReferenceMeasure := by
          rw [(show ∫⁻ x in s, ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) ∂gmcReferenceMeasure = ∫⁻ x in s, refWeight x * ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) ∂volume by rw [gmcReferenceMeasure]; exact setLIntegral_withDensity_eq_setLIntegral_mul volume refWeight_measurable hwick hs)]
          apply setLIntegral_congr_fun hs
          intro x hx
          calc
            ENNReal.ofReal (Real.exp
                (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
                  normPlus x ^ (-4 : ℝ)) =
                ENNReal.ofReal (Real.exp
                  (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) *
                    ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) :=
                ENNReal.ofReal_mul (Real.exp_pos _).le
            _ = refWeight x * ENNReal.ofReal
                  (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
                    ∫ ω', Xc ω' x r ^ 2 ∂P)) := by
                simp [refWeight, mul_comm]
      _ = _ := (withDensity_apply _ hs).symm
  let φ : ℂ → ℂ := fun x => x⁻¹
  have hmeas : Measurable φ := by fun_prop
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))
  rw [regularizedGMC_eq_reference_withDensity Xc γ r ω hwick,
    regularizedGMC_eq_reference_withDensity (fun ω y s => Xc ω y⁻¹ s) γ r ω (by change Measurable (w ∘ φ); exact hwick.comp hmeas),
    measurePreserving_involutive_map_withDensity φ gmcReferenceMeasure ⟨hmeas, by simpa [φ] using gmcReferenceMeasure_map_complexInv⟩ (by intro x; simp [φ]) w hwick]

end DOZZ.Proofs
