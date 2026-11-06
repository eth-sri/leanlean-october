module
public import GuthMaynard.Improvement.CubicTimeMeasure
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory Set
namespace GuthMaynard.Improvement

theorem tripleMeasure_ae_interval (ν : Measure ℝ) [SFinite ν] {a b : ℝ}
    (hs : ∀ᵐ t ∂ν, t ∈ Icc a b) :
    ∀ᵐ t : Triple ∂tripleMeasure ν, t.1 ∈ Icc a b ∧ t.2.1 ∈ Icc a b ∧ t.2.2 ∈ Icc a b := by
  unfold tripleMeasure
  pm_8712 t ht
  pm_8712 u hu
  filter_upwards [hs] with v hv
  grind

theorem timeMeasure_ae_interval {μ : ℝ → ℝ} {a b : ℝ}
    (hm : Measurable μ) (hs : ∀ t, t ∉ Icc a b → μ t = 0) :
    ∀ᵐ t ∂timeMeasure μ, t ∈ Icc a b := by
  apply (ae_withDensity_iff hm.ennreal_ofReal).mpr
  filter_upwards with t
  intro ht
  by_contra hn
  simp_all

/-- Only differences within the actual time-support length affect the
cubic kernel integral. No global approximation of K is required. -/
theorem kernelCubic_congr_interval (ν : Measure ℝ) [SFinite ν] {a b : ℝ}
    (hs : ∀ᵐ t ∂ν, t ∈ Icc a b) {K J : ℝ → ℂ}
    (heq : ∀ s, |s| ≤ b-a → K s = J s) : kernelCubic ν K = kernelCubic ν J := by
  unfold kernelCubic
  apply integral_congr_ae
  filter_upwards [tripleMeasure_ae_interval ν hs] with t ht
  have hd : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |u-v| ≤ b-a := by
    intro u hu v hv
    apply abs_le.mpr
    grind
  grind

/-- Local kernel approximation on the time-difference interval suffices
for the actual homogeneous L2 cubic remainder. -/
theorem cubic_local_time_perturbation {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) (hs : ∀ t, t ∉ Icc a b → μ t = 0)
    {K J : ℝ → ℂ} {B e : ℝ} (hK : Measurable K) (hJ : Measurable J)
    (hB : 0 ≤ B) (he : 0 ≤ e)
    (hbK : ∀ s, |s| ≤ b-a → ‖K s‖ ≤ B) (hbJ : ∀ s, |s| ≤ b-a → ‖J s‖ ≤ B)
    (herr : ∀ s, |s| ≤ b-a → ‖K s-J s‖ ≤ e) :
    ‖kernelCubic (timeMeasure μ) K-kernelCubic (timeMeasure μ) J‖ ≤
      3*e*B^2*(Real.sqrt (b-a))^3*(Real.sqrt (∫ t, μ t^2))^3 := by
  let := timeMeasure_finite hi
  let E := {s : ℝ | |s| ≤ b-a}
  have hE : MeasurableSet E := measurableSet_le measurable_id.abs measurable_const
  have hkb : ∀ s, ‖E.indicator K s‖ ≤ B := by
    pm_4539 hbK hB
  have hjb : ∀ s, ‖E.indicator J s‖ ≤ B := by
    pm_4539 hbJ hB
  have heb : ∀ s, ‖E.indicator K s-E.indicator J s‖ ≤ e := by
    pm_4539 herr he
  have hkEq := kernelCubic_congr_interval (timeMeasure μ) (timeMeasure_ae_interval hm hs)
    (K := K) (J := E.indicator K) (fun s hx => (indicator_of_mem (show s ∈ E from hx) K).symm)
  have hjEq := kernelCubic_congr_interval (timeMeasure μ) (timeMeasure_ae_interval hm hs)
    (K := J) (J := E.indicator J) (fun s hx => (indicator_of_mem (show s ∈ E from hx) J).symm)
  rw [hkEq,hjEq]
  exact cubic_time_density_perturbation hab hm h0 hi h2 hs (hK.indicator hE) (hJ.indicator hE) hB he hkb hjb heb

end GuthMaynard.Improvement
