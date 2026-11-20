/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRadialChart
public import DOZZ.GMC.OpenChartCompacts
public import DOZZ.MeasureTheory.FiniteOnChart
/-! Joint measurability of locally finite chart masses via finite restrictions. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A measurable code for a weighted chart mass, valid on locally finite chart inputs. -/
noncomputable def chartMassCode {A : Type*} (U : Set ℂ) (hU : IsOpen U) (F : A × ℂ → ℝ≥0∞)
    (p : A × Measure ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ∫⁻ x, F (p.1,x) ∂(finiteRestrictionOnSet (chartCompacts U hU n) p.2 : Measure ℂ)

theorem chartMassCode_measurable {A : Type*} [MeasurableSpace A] {U : Set ℂ} (hU : IsOpen U)
    {F : A × ℂ → ℝ≥0∞} (hF : Measurable F) : Measurable (chartMassCode U hU F) := by
  apply Measurable.iSup
  intro n
  exact (measurable_lintegral_finiteMeasure_parameter hF).comp
    (measurable_fst.prodMk ((measurable_finiteRestrictionOnSet _
      ((chartCompacts_spec U hU).1 n).measurableSet).comp measurable_snd))

theorem chartMassCode_eq {A : Type*} {U : Set ℂ} (hU : IsOpen U) (F : A × ℂ → ℝ≥0∞)
    (p : A) (μ : Measure ℂ) (hfin : FiniteOnChart U μ) :
    chartMassCode U hU F (p,μ) = ∫⁻ x in U, F (p,x) ∂μ := by
  obtain ⟨hK, hKU, hKm, hKe, -⟩ := chartCompacts_spec U hU
  have he (n : ℕ) : (finiteRestrictionOnSet (chartCompacts U hU n) μ : Measure ℂ) =
      μ.restrict (chartCompacts U hU n) := by
    simp [finiteRestrictionOnSet, hfin _ (hK n) (hKU n)]
  simp only [chartMassCode, he]
  rw [← setLIntegral_iUnion_of_directed _ hKm.directed_le, hKe]

/-- Local finiteness on the chart suffices for joint measurability. -/
theorem reflected_chart_parameter_mass_measurable
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (U : Set ℂ) (hU : IsOpen U) (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω, FiniteOnChart U (N ω)) (F : A × ℂ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : A × Ω => ∫⁻ x in U, F (p.1, x) ∂N p.2) := by
  convert (chartMassCode_measurable hU hF).comp (measurable_fst.prodMk (hN.comp measurable_snd)) using 1
  funext p
  exact (chartMassCode_eq hU F p.1 (N p.2) (hfin p.2)).symm

noncomputable abbrev reflectedPuncturedMassCode {A : Type*} (F : A × ℂ → ℝ≥0∞) : A × Measure ℂ → ℝ≥0∞ :=
  chartMassCode ({0} : Set ℂ)ᶜ isClosed_singleton.isOpen_compl F

theorem reflected_puncturedMassCode_measurable {A : Type*} [MeasurableSpace A]
    (F : A × ℂ → ℝ≥0∞) (hF : Measurable F) : Measurable (reflectedPuncturedMassCode F) :=
  chartMassCode_measurable isClosed_singleton.isOpen_compl hF

theorem reflected_puncturedMassCode_eq {A : Type*} (F : A × ℂ → ℝ≥0∞) (p : A) (μ : Measure ℂ)
    (hfin : FiniteOnChart ({0} : Set ℂ)ᶜ μ) :
    reflectedPuncturedMassCode F (p,μ) = ∫⁻ x in ({0} : Set ℂ)ᶜ, F (p,x) ∂μ :=
  chartMassCode_eq isClosed_singleton.isOpen_compl F p μ hfin

end DOZZ.Proofs
