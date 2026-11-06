/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.Reflection.StructureContinuity
public import DOZZ.Correlations.Analytic.ParameterDomain
import DOZZ.ShiftEquations.Reflection.RbarContinuity
/-! # Strict parameter neighborhoods for the root continuity argument -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- The three-coordinate finite-insertion bounds recover the canonical extended triple. -/
theorem roots_extendedSeiberg3_of_N {γ a b c}
    (h : ExtendedSeibergN γ ![a, b, c]) : ExtendedSeiberg3 γ a b c := by
  have he : nPointSExp γ ![a, b, c] = sExp γ a b c := by
    simp only [nPointSExp, sExp, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨h.1 0, h.1 1, h.1 2, ?_⟩
  exact lt_min (by simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h.2.1)
    (lt_min (by simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h.2.2 0)
      (lt_min (by simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h.2.2 1) (by simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h.2.2 2)))
/-- Strict extended charges persist when gamma varies near an admissible value. -/
theorem roots_extended_parameters_nhds {γ a b c} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : ExtendedSeiberg3 γ a b c) :
    ∀ᶠ g : ℝ in nhds γ, 0 < g ∧ g < 2 ∧ ExtendedSeiberg3 g a b c := by
  filter_upwards [(continuousAt_id.tendsto.prodMk_nhds tendsto_const_nhds).eventually (extendedSeibergN_mem_nhds (γ, ![a, b, c]) hγ hγ2 (extendedSeibergN_of_extendedSeiberg3 hα))] with g hg
  exact ⟨hg.1, hg.2.1, roots_extendedSeiberg3_of_N hg.2.2⟩
/-- Joint continuity on compact admissible sets gives continuity of the canonical moment in gamma. -/
theorem roots_unitVolume_gamma_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (hM : ∀ g, 0 < g → g < 2 → IsGMCOf P X g (M g))
    (γ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : ExtendedSeiberg3 γ a b c) :
    ContinuousAt (fun g => unitVolumeStructureConstant P (M g) g a b c) γ := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (roots_extended_parameters_nhds hγ hγ2 hα)
  let J := Icc (γ - R / 2) (γ + R / 2)
  let A := fun g : ℝ => (g, (![a, b, c] : Fin 3 → ℝ))
  have hAc : Continuous A := continuous_id.prodMk continuous_const
  have hJdom : ∀ g ∈ J, 0 < g ∧ g < 2 ∧ ExtendedSeiberg3 g a b c := by
    intro g hg
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith only [hg.1, hR], by linarith only [hg.2, hR]⟩
  have hc := continuousOn_unitVolumeStructureConstant P X M hX hM (A '' J) (isCompact_Icc.image hAc) (by rintro q ⟨g, hg, rfl⟩; exact hJdom g hg)
  exact (hc.comp hAc.continuousOn (fun g hg => mem_image_of_mem A hg)).continuousAt (Icc_mem_nhds (by linarith only [hR])
    (by linarith only [hR]))
end DOZZ.Proofs
