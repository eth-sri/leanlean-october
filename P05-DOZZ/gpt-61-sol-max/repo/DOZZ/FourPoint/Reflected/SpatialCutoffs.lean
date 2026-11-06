/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ConditionalCompactLimit
public import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic
/-! Genuine compact test cutoffs exhausting an open spatial region. -/
public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

variable (U : Set ℂ) (hU : IsOpen U) (D : Set ℂ) (hD : IsCompact D) (hDU : D ⊆ U)

include U hU D hD hDU in
/-- The cutoffs equal one eventually at every point of the open region and vanish outside it.
No boundary regularity or measure-dependent choice is needed. -/
theorem reflected_open_compact_cutoffs  :
    ∃ f : ℕ → BoundedContinuousFunction ℂ ℝ,
      (∀ n, EqOn (f n) 1 D) ∧
      (∀ n, IsCompact (tsupport (f n : ℂ → ℝ))) ∧
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ U) ∧
      (∀ n x, f n x ∈ Icc 0 1) ∧
      (∀ x ∈ U, ∀ᶠ n in atTop, f n x = 1) ∧
      (∀ n x, x ∉ U → f n x = 0) := by
  let _  := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  let K : ℕ → Set ℂ := fun n => Subtype.val '' E n
  have hK (n : ℕ) : IsCompact (K n) := (E.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : K n ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hex (n : ℕ) := exists_continuousMap_one_of_isCompact_subset_isOpen ((hK n).union hD) hU
    (union_subset (hKU n) hDU)
  choose g hgK hgc hgU hgb using hex
  let f : ℕ → BoundedContinuousFunction ℂ ℝ := fun n =>
    BoundedContinuousFunction.mkOfBound (g n) 1 (fun x y => by
      exact Real.dist_le_of_mem_Icc_01 (hgb n x) (hgb n y))
  refine ⟨f, fun n x hx => hgK n (Or.inr hx), hgc, hgU, hgb, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hgK m (Or.inl ⟨⟨x, hx⟩, E.subset hm hn, rfl⟩)
  · intro n x hx
    exact image_eq_zero_of_notMem_tsupport (fun hs => hx (hgU n hs))

/-- A continuous weight on the open region becomes an actual bounded compact test after cutting
it off there, even when the original weight is singular on the boundary. -/
theorem reflected_compact_weighted_test (U : Set ℂ) (hU : IsOpen U)
    (f : BoundedContinuousFunction ℂ ℝ) (hf : IsCompact (tsupport (f : ℂ → ℝ)))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (w : ℂ → ℝ) (hw : ContinuousOn w U) :
    ∃ g : BoundedContinuousFunction ℂ ℝ, (∀ x, g x = f x*w x) ∧
      tsupport (g : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) := by
  have hs : tsupport (fun x => f x*w x) ⊆ tsupport (f : ℂ → ℝ) :=
    tsupport_mul_subset_left
  have hc  := continuous_of_tsupport fun x hx =>
    (f.continuous.continuousAt).mul (hw.continuousAt (hU.mem_nhds (hfU (hs hx))))
  have hcomp : HasCompactSupport (fun x => f x*w x) :=
    hf.of_isClosed_subset (isClosed_tsupport _) hs
  let g : BoundedContinuousFunction ℂ ℝ :=
    ⟨⟨fun x => f x*w x, hc⟩, Metric.isBounded_range_iff.mp (hcomp.isCompact_range hc).isBounded⟩
  exact ⟨g, fun _ => rfl, hs⟩

include U hU D hD hDU in
/-- Spatial cutoff removal for a nonnegative weighted mass, including infinite masses, uses
Fatou and the pointwise upper bound. The compact tests are independent of the measure and need
no boundary-null assumption. -/
theorem reflected_open_weighted_mass_approximation 
    (w : ℂ → ℝ) (hw : ContinuousOn w U) (_hwm : Measurable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ g : ℕ → BoundedContinuousFunction ℂ ℝ,
      (∀ n, EqOn (g n) w D) ∧
      (∀ n, IsCompact (tsupport (g n : ℂ → ℝ))) ∧
      (∀ n, tsupport (g n : ℂ → ℝ) ⊆ U) ∧
      (∀ n x, 0 ≤ g n x) ∧
      ∀ μ : Measure ℂ, Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop
          (𝓝 (∫⁻ x in U, ENNReal.ofReal (w x) ∂μ)) := by
  obtain ⟨f, hfD, hfc, hfU, hfb, hfone, hfzero⟩ :=
    reflected_open_compact_cutoffs U hU D hD hDU
  choose g hg hgs using fun n => reflected_compact_weighted_test U hU (f n)
    (hfc n) (hfU n) w hw
  refine ⟨g, (fun n x hx => by rw [hg n x, hfD n hx]; exact one_mul _), fun n => (hfc n).of_isClosed_subset (isClosed_tsupport _) (hgs n),
    fun n => (hgs n).trans (hfU n), ?_, ?_⟩
  · intro n x
    rw [hg n x]
    exact mul_nonneg (hfb n x).1 (hwn x)
  · intro μ
    have he : (∫⁻ x, U.indicator (fun x => ENNReal.ofReal (w x)) x ∂μ) =
        ∫⁻ x in U, ENNReal.ofReal (w x) ∂μ := lintegral_indicator hU.measurableSet _
    rw [← he]
    have hb (n : ℕ) (x : ℂ) : ENNReal.ofReal (g n x) ≤
        U.indicator (fun x => ENNReal.ofReal (w x)) x := by
      rw [hg n x]
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx, ENNReal.ofReal_mul (hfb n x).1]
        exact le_trans (mul_le_mul' (show ENNReal.ofReal (f n x) ≤ 1 by
          simpa using ENNReal.ofReal_le_ofReal (hfb n x).2) le_rfl) (one_mul _).le
      simp_all
    have hp (x : ℂ) : Tendsto (fun n => ENNReal.ofReal (g n x)) atTop
        (𝓝 (U.indicator (fun x => ENNReal.ofReal (w x)) x)) := by
      by_cases hx : x ∈ U
      · refine (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
          U.indicator (fun x => ENNReal.ofReal (w x)) x) atTop
          (𝓝 (U.indicator (fun x => ENNReal.ofReal (w x)) x))).congr' ?_
        filter_upwards [hfone x hx] with n hn
        rw [hg n x, hn, one_mul, indicator_of_mem hx]
      simp_all
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · calc
        _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ :=
          lintegral_congr (fun x => (hp x).liminf_eq.symm)
        _ ≤ _ := lintegral_liminf_le (fun n => (g n).continuous.measurable.ennreal_ofReal)
    · exact limsup_le_of_le (h := Eventually.of_forall fun n => lintegral_mono (hb n))

end DOZZ.Proofs
