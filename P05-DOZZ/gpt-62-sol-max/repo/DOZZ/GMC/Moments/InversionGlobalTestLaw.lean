/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionExhaustion
public import DOZZ.GMC.Construction.GMCIntensityAdapter
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.SubunitSet
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import DOZZ.GMC.Construction.GMCMeasurableVersion
@[expose] public section
open Filter MeasureTheory Set Metric
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- Bounded continuous integrals of finite random measures are measurable up to null sets. -/
theorem finiteMeasure_bcf_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : AEMeasurable M P)
    (hfin : ∀ ω, IsFiniteMeasure (M ω)) (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  let : ∀ ω, IsFiniteMeasure (M ω) := hfin
  have hp := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp f.nnrealPart)).comp_aemeasurable hM
  have hn := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp (-f).nnrealPart)).comp_aemeasurable hM
  have h : AEMeasurable (fun ω =>
      (∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂M ω).toReal -
      (∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂M ω).toReal) P :=
    hp.ennreal_toReal.sub hn.ennreal_toReal
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, Function.comp_def, Pi.sub_apply] using h

section
variable {Ω : Type*} [MeasurableSpace Ω] {k l : ℕ} (P : Measure Ω) (X : Ω → Distr)
  (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ)
  (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hc γ hγ hγ2 hM

/-- Full bounded test-vector inversion law jointly with the reversed radial coordinates.
Compact annular cutoffs exhaust the plane outside its zero atom. -/
theorem gmc_inversion_joint_test_vector_law
    (s : Fin l → ℝ) (f : Fin k → BoundedContinuousFunction ℂ ℝ) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => ∫ x, f j x ∂(M ω).map
      (fun z : ℂ => z⁻¹))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => ∫ x, f j x ∂M ω)) := by
  let  := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm  := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := fun ω => by let := hM.1 ω; infer_instance
  let q := fun n j => f j * gmcInversionCutoff n
  have hqm n j := finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (q n j)
  have hqn n j := finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (q n j)
  have hzero := gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0
  have hNzero : ∀ᵐ ω ∂P, N ω {0} = 0 := by
    filter_upwards [hzero] with ω hω
    change (M ω).map (fun z : ℂ => z⁻¹) {0} = 0
    rw [Measure.map_apply measurable_inv (measurableSet_singleton 0)]
    simpa
  have hV : AEMeasurable (fun ω i => Xc ω 0 (-s i)) P :=
    AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  have hV' : AEMeasurable (fun ω i => Xc ω 0 (s i)) P :=
    AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  have hconv (A : Ω → Measure ℂ) (hA : AEMeasurable A P)
      (hAfin : ∀ ω, IsFiniteMeasure (A ω)) (hAz : ∀ᵐ ω ∂P, A ω {0} = 0) (j : Fin k) :
      TendstoInMeasure P (fun n ω => ∫ x, q n j x ∂A ω) atTop (fun ω => ∫ x, f j x ∂A ω) := by
    apply tendstoInMeasure_of_tendsto_ae fun n =>
      (finiteMeasure_bcf_integral_aemeasurable P A hA hAfin (q n j)).aestronglyMeasurable
    filter_upwards [hAz] with ω hω
    apply inversion_cutoff_integral_tendsto <;> assumption
  apply gmc_limit_joint_test_vector_law _ _ hV hV'
    (fun n ω j => ∫ x, q n j x ∂N ω) (fun n ω j => ∫ x, q n j x ∂M ω)
    (fun ω j => ∫ x, f j x ∂N ω) (fun ω j => ∫ x, f j x ∂M ω)
  · exact fun n => AEMeasurable.of_eval (hqn n)
  · exact fun n => AEMeasurable.of_eval (hqm n)
  · exact AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (f j)
  · exact AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (f j)
  · intro n
    let U := {x : ℂ | 1 / (2 * ((n : ℝ) + 2)) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 3}
    apply gmc_inversion_annular_joint_test_vector_law P X hX Xc hc γ hγ hγ2 M hM U
      (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const))
      (m := 1 / (4 * ((n : ℝ) + 2))) (R := (n : ℝ) + 3)
      (by positivity) (by positivity)
    · intro x hx
      constructor
      · have he : 2 * (1 / (4 * ((n : ℝ) + 2))) = 1 / (2 * ((n : ℝ) + 2)) := by
          field_simp; norm_num
        rw [he]; exact hx.1.le
      · exact hx.2.le
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).1
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).2
  · exact hconv N hNm hNfin hNzero
  · exact hconv M hMm hM.1 hzero

end

/-- Inversion preserves every bounded continuous test vector of a GMC version. -/
theorem gmc_inversion_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : Fin k → BoundedContinuousFunction ℂ ℝ) :
    P.map (fun ω j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)) =
      P.map (fun ω j => ∫ x, f j x ∂M ω) := by
  obtain ⟨Xc, hc, _⟩ := hM.2
  have h := gmc_inversion_joint_test_vector_law P X hX Xc hc γ hγ hγ2 M hM (l := 0) Fin.elim0 f
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := fun ω => by let := hM.1 ω; infer_instance
  have hm (s : Fin 0 → ℝ) : AEMeasurable (fun ω i => Xc ω 0 (s i)) P :=
    AEMeasurable.of_eval fun i => Fin.elim0 i
  exact map_snd_eq_of_joint_law
    ((hm _).prodMk (AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (f j)))
    ((hm _).prodMk (AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (f j))) h

end DOZZ.Proofs
