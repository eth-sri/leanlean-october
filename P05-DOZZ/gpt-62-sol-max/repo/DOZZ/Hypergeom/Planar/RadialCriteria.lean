module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace DOZZ.Proofs

private theorem integrableOn_iff_lintegral_lt_top {α : Type*} [MeasurableSpace α]
    {s : Set α} {μ : Measure α} {f : α → ℝ} (hf : Measurable f)
    (hnonneg : 0 ≤ᵐ[μ.restrict s] f) :
    IntegrableOn f s μ ↔ (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) < ∞ := by
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal hnonneg]
  simp [hf.aestronglyMeasurable]

section
variable (a : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
include hs

/-- Polar integration of a norm power over a measurable set of radii. -/
private theorem lintegral_norm_rpow_preimage :
    (∫⁻ z : ℂ in (fun z => ‖z‖) ⁻¹' s, ENNReal.ofReal (‖z‖ ^ a)) =
      (∫⁻ r : ℝ in s ∩ Ioi 0, ENNReal.ofReal (r ^ (a + 1))) *
        volume (Ioo (-Real.pi) Real.pi) := by
  let F := ((fun z : ℂ => ‖z‖) ⁻¹' s).indicator (fun z => ENNReal.ofReal (‖z‖ ^ a))
  let g := s.indicator (fun r : ℝ => ENNReal.ofReal (r ^ (a + 1)))
  have hg : Measurable g := Measurable.indicator (by fun_prop) hs
  have hangle : volume (Ioo (-Real.pi) Real.pi) ≠ ∞ := by simp [Real.volume_Ioo]
  calc
    _ = ∫⁻ z, F z := (lintegral_indicator (hs.preimage measurable_norm) _).symm
    _ = ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm F).symm
    _ = ∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, g p.1 := by
      rw [Complex.polarCoord_target]
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hr : 0 < p.1 := hp.1
      have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
      have hm : Complex.polarCoord.symm p ∈ (fun z : ℂ => ‖z‖) ⁻¹' s ↔ p.1 ∈ s := by
        simp only [mem_preimage, hn]
      dsimp [g, F]
      by_cases h : p.1 ∈ s
      · rw [indicator_of_mem h, indicator_of_mem (hm.mpr h), hn,
          ← ENNReal.ofReal_mul hr.le, Real.rpow_add hr, Real.rpow_one, mul_comm]
      · simp only [indicator_of_notMem h, indicator_of_notMem (hm.not.mpr h), mul_zero]
    _ = _ := by
      have hm : Measurable (fun p : ℝ × ℝ => g p.1) := hg.comp measurable_fst
      rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
      simp only [lintegral_const, Measure.restrict_apply_univ]
      rw [lintegral_mul_const' _ _ hangle, setLIntegral_indicator hs]

private theorem integrableOn_norm_rpow_preimage :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ a) ((fun z : ℂ => ‖z‖) ⁻¹' s) ↔
      IntegrableOn (fun r : ℝ => r ^ (a + 1)) (s ∩ Ioi 0) := by
  have hnn : 0 ≤ᵐ[volume.restrict (s ∩ Ioi 0)] (fun r : ℝ => r ^ (a + 1)) := by
    filter_upwards [ae_restrict_mem (hs.inter measurableSet_Ioi)] with r hr
    exact Real.rpow_nonneg hr.2.le _
  rw [integrableOn_iff_lintegral_lt_top (by fun_prop) (ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _), integrableOn_iff_lintegral_lt_top (by fun_prop) hnn, lintegral_norm_rpow_preimage a hs, Real.volume_Ioo]
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_left h.ne
    (ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])).ne',
    fun h => ENNReal.mul_lt_top h ENNReal.ofReal_lt_top⟩

end

section
variable (s R : ℝ) (hR : 0 < R)
include hR

theorem integrableOn_norm_rpow_ball_iff :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.ball 0 R) volume ↔ -2 < s := by
  have hb : Metric.ball (0 : ℂ) R = (fun z : ℂ => ‖z‖) ⁻¹' Iio R := by
    ext z; simp [Metric.mem_ball]
  rw [hb, integrableOn_norm_rpow_preimage s measurableSet_Iio, inter_comm]
  change IntegrableOn _ (Ioo 0 R) ↔ _
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  constructor <;> intro h <;> linarith

theorem integrableOn_norm_rpow_ball_compl_iff :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.ball 0 R)ᶜ volume ↔ s < -2 := by
  have hb : (Metric.ball (0 : ℂ) R)ᶜ = (fun z : ℂ => ‖z‖) ⁻¹' Ici R := by
    ext z; simp [Metric.mem_ball, not_lt]
  have hi : Ici R ∩ Ioi 0 = Ici R := inter_eq_left.mpr fun _ hr => hR.trans_le hr
  rw [hb, integrableOn_norm_rpow_preimage s measurableSet_Ici, hi,
    ← integrableOn_congr_set_ae (μ := volume) (Ioi_ae_eq_Ici (a := R)), integrableOn_Ioi_rpow_iff hR]
  constructor <;> intro h <;> linarith

end

end DOZZ.Proofs
