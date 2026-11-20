/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GMC.Construction.LowerBoxBasis
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! Measurable versions for random measures defined by weak limits in probability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set MeasurableSpace
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (M : Ω → Measure ℂ)
include Ω X hX hXc

theorem gmc_testIntegral_aemeasurable
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω))
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  exact (hconv f).aemeasurable fun r =>
    (measurable_integral_of_measurable_measure (regularizedGMC_measurable P X hX Xc hXc γ r)
      f.continuous.stronglyMeasurable).aemeasurable

private theorem totalMass_real_aemeasurable
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω)) :
    AEMeasurable (fun ω => (M ω Set.univ).toReal) P := by
  have hInt  :=
    gmc_testIntegral_aemeasurable P X hX γ Xc hXc M hconv
      (1 : BoundedContinuousFunction ℂ ℝ)
  have hEq : (fun ω => ∫ x, (1 : ℝ) ∂M ω) =
      fun ω => (M ω Set.univ).toReal := by
    funext ω
    rw [integral_const]
    simp [Measure.real_def]
  exact hInt.congr (ae_of_all P (fun ω => congrFun hEq ω))

private theorem lowerBox_realMass_aemeasurable (hMfinite : ∀ ω, IsFiniteMeasure (M ω))
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω))
    (i : ℚ × ℚ) :
    AEMeasurable (fun ω => (M ω (gmcLowerBox i)).toReal) P := by
  have hseq : ∀ n, AEMeasurable
      (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) P := by
    intro n
    apply gmc_testIntegral_aemeasurable <;> assumption
  exact aemeasurable_of_tendsto_metrizable_ae' hseq (by
    filter_upwards [] with ω
    have hfiniteω  := hMfinite ω
    simpa [Measure.real_def] using gmcLowerBoxApprox_integral_tendsto i (M ω))

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX γ hγ hγ2 hM

theorem equatorGFF_GMC_measurable_version :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ (∀ ω, IsFiniteMeasure (N ω)) ∧
      ∀ᵐ ω ∂P, M ω = N ω := by
  classical
  rcases hM with ⟨hMfinite, Xc, hXc, hconv⟩
  let coordinate  := fun i ω =>
    (M ω (gmcBasisSet i)).toReal
  have hcoordinate : ∀ i, AEMeasurable (coordinate i) P := by
    intro i
    cases i with
    | none =>
        simpa [coordinate, gmcBasisSet] using
          totalMass_real_aemeasurable P X hX γ Xc hXc M hconv
    | some i =>
        simpa [coordinate, gmcBasisSet] using
          lowerBox_realMass_aemeasurable P X hX γ Xc hXc M hMfinite hconv i
  let coordinateMeas  :=
    fun i => (hcoordinate i).mk (coordinate i)
  have hcoordinateMeas  :=
    fun i => (hcoordinate i).measurable_mk
  have hcoordinateAE  :=
    ae_all_iff.mpr fun i => (hcoordinate i).ae_eq_mk
  let bad  := {ω | ∃ i, coordinate i ω ≠ coordinateMeas i ω}
  have hbad : P bad = 0 := by
    simpa [bad] using (ae_iff.mp hcoordinateAE)
  obtain ⟨badMeas, hbadSub, hbadMeasurable, hbadZero⟩ :=
    exists_measurable_superset_of_null hbad
  let good  := badMeasᶜ
  have hgoodMeasurable  := hbadMeasurable.compl
  have hgood : ∀ᵐ ω ∂P, ω ∈ good := by
    rw [ae_iff]
    simpa [good] using hbadZero
  have hcoordinate_eq : ∀ ω, ω ∈ good → ∀ i,
      coordinate i ω = coordinateMeas i ω := by
    intro ω hω i
    by_contra hne
    change ω ∉ badMeas at hω
    exact hω (hbadSub ⟨i, hne⟩)
  let N  := fun ω => if ω ∈ good then M ω else 0
  have hNfinite : ∀ ω, IsFiniteMeasure (N ω) := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa [N, hω] using hMfinite ω
    · simpa [N, hω] using (inferInstance : IsFiniteMeasure (0 : Measure ℂ))
  have hEvalMeasurable (i : Option (ℚ × ℚ)) :
      Measurable (fun ω => N ω (gmcBasisSet i)) := by
    have hEval : (fun ω => N ω (gmcBasisSet i)) =
        fun ω => if ω ∈ good then ENNReal.ofReal (coordinateMeas i ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ good
      · have hcoord := hcoordinate_eq ω hω i
        have hMω  := hMfinite ω
        have hfiniteSet  :=
          measure_ne_top (M ω) (gmcBasisSet i)
        simp [N, hω]
        calc
          M ω (gmcBasisSet i) = ENNReal.ofReal (M ω (gmcBasisSet i)).toReal :=
            (ENNReal.ofReal_toReal hfiniteSet).symm
          _ = ENNReal.ofReal (coordinateMeas i ω) := by rw [← hcoord]
      · simp [N, hω]
    rw [hEval]
    exact Measurable.ite hgoodMeasurable
      (ENNReal.measurable_ofReal.comp (hcoordinateMeas i)) measurable_const
  have hNmeasurable : Measurable N := by
    have hbasic : ∀ s ∈ gmcBasisFamily, Measurable (fun ω => N ω s) := by
      rintro s ⟨i, rfl⟩
      exact hEvalMeasurable i
    exact @Measurable.measure_of_isPiSystem Ω ℂ _ _ N hNfinite gmcBasisFamily
      (BorelSpace.measurable_eq.trans gmcBasisFamily_generate.symm) gmcBasisFamily_pi hbasic (by
      simpa [gmcBasisSet] using hEvalMeasurable none)
  refine ⟨N, hNmeasurable, hNfinite, ?_⟩
  filter_upwards [hgood] with ω hω
  simp [N, hω]

/-- An arbitrary GMC version is almost-everywhere measurable as a measure. -/
theorem equatorGFF_GMC_aemeasurable : AEMeasurable M P := by
  obtain ⟨N, hNm, _, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  exact hNm.aemeasurable.congr (hMN.mono (fun _ hω => hω.symm))

/-- The finite-measure-valued version of GMC measurability. -/
theorem equatorGFF_finiteGMC_aemeasurable :
    AEMeasurable (fun ω => (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ)) P :=
  (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM).subtype_mk

end

end DOZZ.Proofs
