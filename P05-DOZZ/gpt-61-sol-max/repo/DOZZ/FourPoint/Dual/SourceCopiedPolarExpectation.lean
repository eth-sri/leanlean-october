/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRegionRegroup
public import DOZZ.Probability.RealMeasureTranslate
public import DOZZ.FourPoint.Dual.FullPathCarrier
public import DOZZ.FourPoint.Dual.PathPolarTransport
import Mathlib.Tactic
/-! Exact source-to-copied polar expectation transport on the common full-path carrier. -/
public section
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
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
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
  let _  := hX.1
  let A := originRadialPath Xc
  let O := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  let O' := fun ω : Ω × Ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hO : AEMeasurable O P := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx hx0
    have hxzero := mem_singleton_iff.mp hx0
    exact hx.2 (by simp [hxzero])
  have hO' : AEMeasurable O' (P.prod P) :=
    reflected_copied_region_mass_aemeasurable P A N hA hNm hfin γ U hU.measurableSet hU0 _
      (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  let ZT := fun ω => (Z ω).map (fun s : ℝ => s-(T : ℝ))
  have hZT : AEMeasurable ZT P := (Measure.measurable_map _ (measurable_id.sub_const _)).comp_aemeasurable hZ.2.2.2.1
  have hZTfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, ZT ω (Icc a b) < ⊤ :=
    hZ.2.2.2.2.1.mono (fun ω hω => realMeasure_map_sub_Icc_lt_top hω T)
  have he := dual_path_outer_polar_integral_transport P (P.prod P) P A (fun ω => A ω.1)
    O O' ZT hA hA.comp_fst hO hO' hZT hZTfin hlaw γ (Q γ-α₁) h p z T
  have hb := dual_source_radial_scale_eq_path_ae P Xc hcont γ (Q γ-α₁) h z
  apply Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hb] with ω hω
  rw [hω]

end DOZZ.Proofs
