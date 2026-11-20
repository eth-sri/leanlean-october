/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.CompactOpen

/-! Measurability of a cutoff chaos built from a continuous sample circle field. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Coordinate measurability and all-sample continuity make a random continuous circle function
measurable for the Borel structure on the compact-open continuous-map space. -/
theorem measurable_circleContinuousMap
    {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → ℂ → ℝ)
    (hY : ∀ x, Measurable (fun ω => Y ω x))
    (hcont : ∀ ω, Continuous (Y ω)) :
    Measurable (fun ω => (⟨Y ω, hcont ω⟩ : C(ℂ, ℝ))) :=
  ContinuousMap.measurable_iff_eval.mpr hY

/-- A fixed-radius circle process has a measurable realization as a random continuous function.
Its coordinates agree almost surely with the supplied `IsCircleAverage` witness. -/
theorem exists_measurable_continuousCircleProfile
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) :
    ∃ Z : Ω → C(ℂ, ℝ),
      (∀ x, Measurable (fun ω => Z ω x)) ∧
      (∀ x, (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r) ∧
      Measurable Z := by
  classical
  let _  := hX.1
  let Y : ℂ × ℝ → Ω → ℝ := fun p ω => Xc ω p.1 p.2
  have hprocess := circleAverage_isGaussianProcess P X Xc hX hXc
  have hmeas (p : ℂ × ℝ) : Measurable (Y p) := (hXc.1 p.2).comp (measurable_id.prodMk measurable_const)
  have hmem (p : ℂ × ℝ) := hXc.2.1 p.1 p.2
  have hmean (p : ℂ × ℝ) := hprocess.2 p.1 p.2
  have hcov (p q : ℂ × ℝ) :
      ProbabilityTheory.covariance (Y p) (Y q) P =
        ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2 := by
    rw [ProbabilityTheory.covariance_comm]
    simpa [Y, gaussianCovariance, ProbabilityTheory.covariance, hmean q, hmean p] using
      (isCircleAverage_covariance P X hX Xc hXc q.1 p.1 q.2 p.2)
  obtain ⟨Z, hZm, hZcont, hZae⟩ :=
    exists_continuous_circleL2_modification_at_radius Y hmeas hmem hprocess.1 hmean hcov r
  exact Exists.intro (fun ω => { toFun := fun x => Z x ω, continuous_toFun := hZcont ω })
    ⟨hZm, ⟨hZae, measurable_circleContinuousMap (fun ω x => Z x ω) hZm fun ω => hZcont ω⟩⟩

/-- The regularized GMC measure is a measurable function of an all-sample continuous circle
profile, with deterministic variance and reference weight. -/
theorem continuousCircleCutoffMeasure_measurable
    (V : ℂ → ℝ) (hV : Measurable V) (γ : ℝ) :
    Measurable (fun F : C(ℂ, ℝ) => volume.withDensity (fun x => ENNReal.ofReal
      (Real.exp (γ * F x - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)))) := by
  classical
  let density : C(ℂ, ℝ) × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal
    (Real.exp (γ * q.1 q.2 - γ ^ 2 / 2 * V q.2) * normPlus q.2 ^ (-4 : ℝ))
  have hnorm : Measurable (fun x : ℂ => normPlus x) := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  have heval  :=
    (continuous_eval : Continuous fun q : C(ℂ, ℝ) × ℂ => q.1 q.2).measurable
  have hdensity : Measurable density := by
    fun_prop
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let G  := fun q => if q.2 ∈ A then density q else 0
  have hG : Measurable G :=
    Measurable.ite (hA.preimage measurable_snd) hdensity measurable_const
  have hsection (F : C(ℂ, ℝ)) :
      (∫⁻ x in A, density (F, x) ∂volume) = ∫⁻ x, G (F, x) ∂volume := by
    rw [← lintegral_indicator hA]
    rfl
  have hEval : (fun F : C(ℂ, ℝ) =>
      (volume.withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * F x - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)))) A) =
      fun F => ∫⁻ x, G (F, x) ∂volume := by
    funext F
    rw [withDensity_apply _ hA]
    apply hsection
  rw [hEval]
  exact hG.lintegral_prod_right'

end DOZZ.Proofs
