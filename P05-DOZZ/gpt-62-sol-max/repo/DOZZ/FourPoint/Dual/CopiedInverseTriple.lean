/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CopyOrdering
public import DOZZ.FourPoint.Dual.SourceDecouplingBound
import Mathlib.Tactic
public import DOZZ.MeasureTheory.FiniteOnChart
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! The literal copied inverse expectation in source radial/outer/inner coordinates. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Reorder the actual independently reinserted kernel masses before converting their
inverse expectation to real. All parameterized masses are measurable on the lateral carrier. -/
theorem dual_copied_inverse_moment_triple
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ) (hA : AEMeasurable (originRadialPath Xc) P)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (γ α₁ α₂ α₃ p s r : ℝ) (z : ℂ) :
    dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z s r =
      ∫⁻ v : (Ω × Ω) × Ω,
        ((∫⁻ x in reflected_innerRegion s,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc v.1.1) x) ∂N v.2)+
         (∫⁻ x in reflected_outerRegion r,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc v.1.1) x) ∂N v.1.2))^(-p)
          ∂(P.prod P).prod P := by
  let J := fun U (a : TwoSidedPath) ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
  have hm {W : Set ℂ} (hW : IsOpen W) (hW0 : W ⊆ ({0} : Set ℂ)ᶜ) :
      Measurable (fun v : TwoSidedPath × Ω => J W v.1 v.2) :=
    reflected_reinserted_region_measurable hN hfin γ hW.measurableSet hW0
      (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hi := hm (reflected_innerRegion_open s) (reflected_innerRegion_punctured _)
  have ho := hm (reflected_outerRegion_open (r)) (reflected_outerRegion_punctured _)
  let F : TwoSidedPath × (Ω × Ω) → ℝ≥0∞ := fun v =>
    (J (reflected_innerRegion s) v.1 v.2.1+J (reflected_outerRegion r) v.1 v.2.2)^(-p)
  exact dual_radial_copy_lintegral_regroup P (originRadialPath Xc) hA F (((hi.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (ho.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).pow_const (-p))

end DOZZ.Proofs
