/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTilt
public import DOZZ.GMC.Construction.GMCGeneralTiltScalarLimit
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Raw-field measurable circle cutoffs and scalar versions of their GMC limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- A canonical circle witness with raw-joint measurability at each fixed radius. -/
theorem exists_raw_equatorGFF_circle_average_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    X (hX : IsEquatorGFF P X) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
      ∀ r, Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => Xc p.1 p.2 r) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨f, W, Y, hgap, hcross, hW, hY, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_circle_L2_geometry X hX
  have hmem (p : ℂ × ℝ) := (hY p).2.2.1
  choose Z hZmeas hZcont hZeq using (fun r => exists_continuous_circleL2_modification_at_radius Y (fun p => (hY p).2.1) hmem hproc hmean hcov r)
  choose G hGjoint hGae using (fun r => exists_raw_joint_continuous_modification P (equatorGFFRawDistributionSigma X) (fun ω x => Z r x ω) (ae_of_all P (hZcont r)) (fun x => ⟨Y (x, r), (hY (x, r)).1, (hZeq r x).symm⟩))
  let Xc : Ω → ℂ → ℝ → ℝ := fun ω x r => G r ω x
  have hprod : (equatorGFFRawDistributionSigma X).prod (borel ℂ) ≤ mΩ.prod (borel ℂ) := by
    rw [MeasurableSpace.prod, MeasurableSpace.prod]
    exact sup_le_sup (MeasurableSpace.comap_mono (by dsimp [equatorGFFRawDistributionSigma]; exact (measurable_pi_iff.mpr (fun g => (hX.2 g).1)).comap_le)) le_rfl
  have hXcY x r : (fun ω => Xc ω x r) =ᵐ[P] fun ω => Y (x, r) ω := by
    filter_upwards [hGae r, hZeq r x] with ω hG hZ
    exact (hG x).trans hZ
  refine ⟨Xc, ?_, hGjoint⟩
  refine ⟨(fun r => (hGjoint r).mono hprod le_rfl), fun x r => ?_, ?_⟩
  · exact MemLp.ae_eq (hXcY x r).symm (hmem (x, r))
  · intro x r g hg
    let p := (x, r)
    exact tendsto_eLpNorm_sub_of_L2_versions P (fun n => (equatorGFF_test_memLp X hX (g n)).toLp (fun ω => X ω (g n))) (W p)
      (fun n ω => X ω (g n)) (fun ω => Xc ω x r)
      (fun n => (equatorGFF_test_memLp X hX (g n)).coeFn_toLp.symm)
      ((hXcY x r).trans (hY p).2.2.2.1) (equatorGFF_testL2_tendsto_to_circle_limit X hX x r (f p) (hgap p) (W p) (hW p) g hg)

/-- Raw-joint measurability of a circle field makes each cutoff measure raw measurable. -/
theorem regularizedGMC_raw_measurable_of_joint
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc) γ r
    (hRaw : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
      (fun p : Ω × ℂ => Xc p.1 p.2 r)) :
    Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => regularizedGMC P Xc γ r ω) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  have hVmeas : Measurable (fun x => ∫ ω, Xc ω x r ^ 2 ∂P) := by
    let q : ℂ → Ω → ℝ := fun x ω => Xc ω x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase := (hXc.1 r).comp measurable_swap
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [(show (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) = fun p => Xc p.2 p.1 r * Xc p.2 p.1 r by funext p; ring)]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω, q x ω ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  let density : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  have hdensity : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)] density := by
    have : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => normPlus p.2) := (show Measurable (fun x => normPlus x) by unfold normPlus; exact measurable_const.max measurable_norm).comp measurable_snd
    dsimp [density]
    exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (by change Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)] ((fun p : Ω × ℂ => γ * Xc p.1 p.2 r) - fun p => γ ^ 2 / 2 * V p.2); simpa [mul_comm] using (hRaw.const_mul γ).sub (((show Measurable V by simpa [V] using hVmeas).comp measurable_snd).const_mul (γ ^ 2 / 2)))).mul (by fun_prop))
  refine @Measure.measurable_of_measurable_coe ℂ Ω _
    (equatorGFFRawDistributionSigma X) (fun ω => regularizedGMC P Xc γ r ω) ?_
  intro A hA
  let G : Ω × ℂ → ℝ≥0∞ := fun p => if p.2 ∈ A then density p else 0
  have hEval : (fun ω => regularizedGMC P Xc γ r ω A) =
      fun ω => ∫⁻ x, G (ω, x) ∂volume := by
    funext ω
    change (volume.withDensity (fun x => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ))) A) = _
    rw [withDensity_apply _ hA]
    change (∫⁻ x in A, density (ω, x) ∂volume) = _
    exact (fun ω => by rw [← lintegral_indicator hA]; apply lintegral_congr; intro x; by_cases hx : x ∈ A <;> simp [G, hx]) ω
  rw [hEval]
  exact @Measurable.lintegral_prod_right' Ω ℂ
    (equatorGFFRawDistributionSigma X) (borel ℂ) volume _ G (Measurable.ite (hA.preimage measurable_snd) hdensity measurable_const)

/-- Every bounded-continuous test integral of an `IsGMCOf` limit has a raw-measurable proxy. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    γ (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] g := by
  rcases hM with ⟨_, XcOld, hXcOld, hconvOld⟩
  obtain ⟨Xc, hXc, hRaw⟩ := exists_raw_equatorGFF_circle_average_witness X hX
  have hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω) := by
    intro f
    have hEq r :
        (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
          fun ω => ∫ x, f x ∂regularizedGMC P XcOld γ r ω := by
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX
        Xc XcOld hXc hXcOld γ r] with ω hω
      rw [hω]
    exact TendstoInMeasure.congr (fun r => (hEq r).symm)
      (Filter.Eventually.of_forall fun _ => rfl) (hconvOld f)
  exact equatorGFF_GMC_testIntegral_raw_measurable_version
    P X hX γ Xc hXc M hconv (fun r => regularizedGMC_raw_measurable_of_joint P X hX Xc hXc γ r (hRaw r)) f

end DOZZ.Proofs
