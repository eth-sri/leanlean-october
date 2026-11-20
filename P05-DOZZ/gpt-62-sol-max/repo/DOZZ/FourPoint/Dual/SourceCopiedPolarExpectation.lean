/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceCopiedOuterLaw
public import DOZZ.FourPoint.Dual.PathPolarTransport
import Mathlib.Tactic
public import DOZZ.MeasureTheory.FiniteOnChart
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! Exact source-to-copied polar expectation transport on the common full-path carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The original source outer/restart polar increment equals the copied exterior/path
increment, with an independent translated inner lateral copy. The full path law preserves
both terminal likelihood and future Brownian increments. -/
theorem dual_source_copied_polar_increment_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (α₁ α₂ α₃ ξ h p : ℝ) (z : ℂ) (T : ℝ≥0)
    (hlaw : P.map (fun ω => (originRadialPath Xc ω,dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) =
      (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
        ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))) :
    let A := originRadialPath Xc
    let O := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
    let O' := fun ω : Ω × Ω => ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2
    let V := fun a ω => ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath T (radialPositiveHalf a) (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z ω).map (fun s => s-(T : ℝ))
    (∫ ω : Ω × Ω, ((O ω.1).toReal+dual_radial_scale γ (Q γ-α₁) h Xc z ω.1*
      (V (A ω.1) ω.2).toReal)^(-p)-(O ω.1).toReal^(-p) ∂P.prod P) =
    ∫ ω : (Ω × Ω) × Ω,
      ((O' ω.1).toReal+dualPathRadialScale γ (Q γ-α₁) h z (A ω.1.1)*
        (V (A ω.1.1) ω.2).toReal)^(-p)-(O' ω.1).toReal^(-p) ∂(P.prod P).prod P := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let O := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  let O' := fun ω : Ω × Ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hO : AEMeasurable O P := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hF := reflected_reinserted_region_measurable hNm hfin γ
    (reflected_outerRegion_open (‖z‖ ^ (1 - ξ))).measurableSet (reflected_outerRegion_punctured _)
    (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hO' : AEMeasurable O' (P.prod P) :=
    hF.comp_aemeasurable (hA.comp_fst.prodMk measurable_snd.aemeasurable)
  let ZT := fun ω => (Z ω).map (fun s : ℝ => s-(T : ℝ))
  have hZT : AEMeasurable ZT P := (Measure.measurable_map _ (measurable_id.sub_const _)).comp_aemeasurable hZ.2.2.2.1
  have hZTfin := ae_map_sub_const_lt_top_Icc P Z (T : ℝ) hZ.2.2.2.2.1
  have he := dual_path_outer_polar_integral_transport P (P.prod P) P A (fun ω => A ω.1)
    O O' ZT hA hA.comp_fst hO hO' hZT hZTfin hlaw γ (Q γ-α₁) h p z T
  have hb := dual_source_radial_scale_eq_path_ae P Xc hcont γ (Q γ-α₁) h z
  apply Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hb] with ω hω
  rw [hω]

end DOZZ.Proofs
