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


/-- A fixed-radius circle process has a measurable realization as a random continuous function.
Its coordinates agree almost surely with the supplied `IsCircleAverage` witness. -/
theorem exists_measurable_continuousCircleProfile
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc) r :
    ∃ Z : Ω → C(ℂ, ℝ),
      (∀ x, Measurable (fun ω => Z ω x)) ∧
      (∀ x, (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r) ∧
      Measurable Z := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let Y : ℂ × ℝ → Ω → ℝ := fun p ω => Xc ω p.1 p.2
  have hprocess := circleAverage_isGaussianProcess P X Xc hX hXc
  have hmean (p : ℂ × ℝ) := hprocess.2 p.1 p.2
  obtain ⟨Z, hZm, hZcont, hZae⟩ :=
    exists_continuous_circleL2_modification_at_radius Y (fun p => (hXc.1 p.2).comp (measurable_id.prodMk measurable_const)) (fun p => hXc.2.1 p.1 p.2) hprocess.1 hmean (fun p q => by rw [ProbabilityTheory.covariance_comm]; simpa [Y, gaussianCovariance, ProbabilityTheory.covariance, hmean q, hmean p] using (isCircleAverage_covariance P X hX Xc hXc q.1 p.1 q.2 p.2)) r
  let Z0 : Ω → ℂ → ℝ := fun ω x => Z x ω
  have hZ0cont (ω : Ω) := hZcont ω
  refine ⟨(fun ω => ⟨Z0 ω, hZ0cont ω⟩), ?_, ?_, ((fun Y hY hcont => ContinuousMap.measurable_iff_eval.mpr hY) Z0 hZm hZ0cont)⟩
  · intro x
    exact hZm x
  · intro x
    exact hZae x

/-- The regularized GMC measure is a measurable function of an all-sample continuous circle
profile, with deterministic variance and reference weight. -/
theorem continuousCircleCutoffMeasure_measurable
    V (hV : Measurable V) γ :
    Measurable (fun F : C(ℂ, ℝ) => volume.withDensity (fun x => ENNReal.ofReal
      (Real.exp (γ * F x - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)))) := by
  classical
  let density : C(ℂ, ℝ) × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal
    (Real.exp (γ * q.1 q.2 - γ ^ 2 / 2 * V q.2) * normPlus q.2 ^ (-4 : ℝ))
  have : Measurable (fun x => normPlus x) := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let G : C(ℂ, ℝ) × ℂ → ℝ≥0∞ := fun q => if q.2 ∈ A then density q else 0
  have hEval : (fun F : C(ℂ, ℝ) =>
      (volume.withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * F x - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)))) A) =
      fun F => ∫⁻ x, G (F, x) ∂volume := by
    funext F
    rw [withDensity_apply _ hA]
    change (∫⁻ x in A, density (F, x) ∂volume) = _
    exact (fun F => by rw [← lintegral_indicator hA]; apply lintegral_congr; intro x; by_cases hx : x ∈ A <;> simp [G, hx]) F
  rw [hEval]
  exact (Measurable.ite (hA.preimage measurable_snd) (by dsimp [density]; fun_prop) measurable_const).lintegral_prod_right'

end DOZZ.Proofs
