module

public import Mathlib.Probability.Martingale.Convergence
public import HypoellipticAleksandrov.Measure.ParabolicDyadicAverage
public import HypoellipticAleksandrov.Measure.ParabolicDyadicGeneration
import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Differentiation along parabolic dyadic cells

This module proves almost-everywhere convergence of the explicit complete-generation
parabolic dyadic averages.  Applying that convergence to a measurable-set indicator gives
eventual strict density in every sufficiently fine addressed cell containing the point.

The argument uses conditional-expectation convergence for the finite reference-cell measure.
It does not use metric differentiation or perform the later maximal dense-cell selection.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section
open scoped ENNReal

theorem parabolicDyadicCheckpointAverage_tendsto_ae
    (d : ℕ) (f : ParabolicDyadicReferenceSpace d → ℝ)
    (hf : Integrable f (parabolicDyadicReferenceMeasure d)) :
    ∀ᵐ z ∂parabolicDyadicReferenceMeasure d,
      Tendsto (fun n => parabolicDyadicCheckpointAverage d n f z)
        atTop (nhds (f z)) := by
  classical
  let : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  let f' := hf.1.mk f
  have hff' : f =ᵐ[parabolicDyadicReferenceMeasure d] f' := by
    simpa only [f'] using hf.1.ae_eq_mk
  have hf' :=
    hf.congr hff'
  have hf'meas : StronglyMeasurable[⨆ k, parabolicDyadicFiltration d k] f' := by
    rw [iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace]
    simpa only [f'] using hf.1.stronglyMeasurable_mk
  have hcond :=
    hf'.tendsto_ae_condExp hf'meas
  have havg : ∀ᵐ z ∂parabolicDyadicReferenceMeasure d, ∀ n,
      parabolicDyadicCheckpointAverage d n f z =
        ((parabolicDyadicReferenceMeasure d)[f' |
          parabolicDyadicFiltration d ((d + 2) * n)]) z := by
    rw [ae_all_iff]
    intro n
    have _h_xinl_0 : parabolicDyadicCheckpointAverage d n f =ᵐ[parabolicDyadicReferenceMeasure d]
      (parabolicDyadicReferenceMeasure d)[f |
        parabolicDyadicFiltration d ((d + 2) * n)] := by
      classical
      letI : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
        ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
      apply ae_eq_condExp_of_forall_setIntegral_eq
        ((parabolicDyadicFiltration d).le ((d + 2) * n)) hf
      · intro s _ _
        exact (integrable_parabolicDyadicCheckpointAverage d n f).integrableOn
      · intro s hs _
        change MeasurableSet[MeasureTheory.Filtration.seq
          (parabolicDyadicFiltration d) ((d + 2) * n)] s at hs
        change MeasurableSet[MeasurableSpace.generateFrom
          (memPartition (parabolicDyadicGenerator d) ((d + 2) * n))] s at hs
        obtain ⟨S, hS, hs_eq⟩ :=
          (MeasurableSpace.measurableSet_generateFrom_memPartition_iff
            (parabolicDyadicGenerator d) ((d + 2) * n) s).mp hs
        have hS_range : (↑S : Set (Set (ParabolicDyadicReferenceSpace d))) ⊆
            Set.range (parabolicDyadicRestrictedCell :
              ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := by
          rw [← memPartition_parabolicDyadicFiltration_checkpoint_eq_range]
          exact hS
        have hmeas : ∀ cell ∈ S, MeasurableSet cell := by
          intro cell hcell
          obtain ⟨index, hindex⟩ := hS_range hcell
          rw [← hindex]
          exact measurableSet_parabolicDyadicRestrictedCell index
        have hdisjoint : (↑S : Set (Set (ParabolicDyadicReferenceSpace d))).Pairwise
            (Function.onFun Disjoint id) := by
          intro cell hcell other hother hne
          exact disjoint_memPartition (parabolicDyadicGenerator d) ((d + 2) * n)
            (hS hcell) (hS hother) hne
        have haverage : ∀ cell ∈ S,
            ∫ x in cell, parabolicDyadicCheckpointAverage d n f x
              ∂parabolicDyadicReferenceMeasure d =
            ∫ x in cell, f x ∂parabolicDyadicReferenceMeasure d := by
          intro cell hcell
          obtain ⟨index, hindex⟩ := hS_range hcell
          rw [← hindex]
          calc
            ∫ x in parabolicDyadicRestrictedCell index,
                parabolicDyadicCheckpointAverage d n f x ∂parabolicDyadicReferenceMeasure d =
                ∫ x in parabolicDyadicRestrictedCell index,
                  parabolicDyadicCellAverage d n f index ∂parabolicDyadicReferenceMeasure d :=
              setIntegral_congr_fun (measurableSet_parabolicDyadicRestrictedCell index)
                fun z hz => parabolicDyadicCheckpointAverage_eq_cellAverage f index z hz
            _ = ∫ x in parabolicDyadicRestrictedCell index,
                  f x ∂parabolicDyadicReferenceMeasure d := by
              rw [setIntegral_const, smul_eq_mul]
              unfold parabolicDyadicCellAverage
              have hpos := parabolicDyadicReferenceMeasure_restrictedCell_real_pos index
              rw [← mul_assoc, mul_inv_cancel₀ hpos.ne']
              exact one_mul _
        have hS_union : ⋃₀ (↑S : Set (Set (ParabolicDyadicReferenceSpace d))) =
            ⋃ cell ∈ S, cell := by
          ext z
          simp
        calc
          ∫ x in s, parabolicDyadicCheckpointAverage d n f x
              ∂parabolicDyadicReferenceMeasure d =
              ∫ x in ⋃ cell ∈ S, cell, parabolicDyadicCheckpointAverage d n f x
                ∂parabolicDyadicReferenceMeasure d := by
            rw [hs_eq, hS_union]
          _ = ∑ cell ∈ S, ∫ x in cell, parabolicDyadicCheckpointAverage d n f x
                ∂parabolicDyadicReferenceMeasure d :=
            integral_biUnion_finset S hmeas hdisjoint fun cell hcell =>
              (integrable_parabolicDyadicCheckpointAverage d n f).integrableOn
          _ = ∑ cell ∈ S, ∫ x in cell, f x ∂parabolicDyadicReferenceMeasure d := by
            apply Finset.sum_congr rfl
            intro cell hcell
            exact haverage cell hcell
          _ = ∫ x in ⋃ cell ∈ S, cell, f x ∂parabolicDyadicReferenceMeasure d :=
            (integral_biUnion_finset S hmeas hdisjoint fun cell hcell => hf.integrableOn).symm
          _ = ∫ x in s, f x ∂parabolicDyadicReferenceMeasure d := by
            rw [hs_eq, hS_union]
      · have _h_xinl_0 : StronglyMeasurable[parabolicDyadicFiltration d ((d + 2) * n)] (parabolicDyadicCheckpointAverage d n f) := by
          unfold parabolicDyadicCheckpointAverage
          simp only [← Finset.sum_apply]
          change StronglyMeasurable[parabolicDyadicFiltration d ((d + 2) * n)]
            (∑ index : ParabolicDyadicIndex d n,
              (parabolicDyadicRestrictedCell index).indicator
                (fun _ => parabolicDyadicCellAverage d n f index))
          apply Finset.stronglyMeasurable_sum
          intro index _
          apply stronglyMeasurable_const.indicator
          apply ProbabilityTheory.measurableSet_partitionFiltration_of_mem
            (measurableSet_parabolicDyadicGenerator d)
          rw [memPartition_parabolicDyadicFiltration_checkpoint_eq_range]
          exact ⟨index, rfl⟩
        exact _h_xinl_0.aestronglyMeasurable
    exact _h_xinl_0.trans
      (condExp_congr_ae hff')
  have hcheckpoint : Tendsto (fun n : ℕ => (d + 2) * n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left n (by omega)
  filter_upwards [hcond, havg, hff'] with z hzcond hzavg hzff'
  have htendsto :=
    hzcond.comp hcheckpoint
  have havgTendsto : Tendsto
      (fun n => parabolicDyadicCheckpointAverage d n f z)
      atTop (nhds (f' z)) :=
    Tendsto.congr' (Eventually.of_forall fun n => (hzavg n).symm) htendsto
  simpa only [hzff'] using havgTendsto

/- At almost every point of a measurable set, every sufficiently fine addressed cell
containing the point has density strictly above the fixed threshold. -/
end

end HypoellipticAleksandrov.Parabolic
