module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxisBounds
import Mathlib.Tactic

/-! # Local boundedness of reflected, kinetically rescaled similarity functions -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology

section
variable (f : ℝ → ℝ) (beta : ℝ)
include f beta

/-- The reflected scalar rescaling, with zero values on the position axis. -/
def scalarRescaled (q : XV 1) : ℝ :=
  if 0 < q.1 0 then Real.rpow (q.1 0) (beta / 3) * f (scalarSimilarity (q.1 0) (q.2 0))
  else if q.1 0 < 0 then Real.rpow (-q.1 0) (beta / 3) *
    f (scalarSimilarity (-q.1 0) (-q.2 0)) else 0

private theorem scalarRescaled_neg (q : XV 1) :
    scalarRescaled f beta (-q) = scalarRescaled f beta q := by
  rcases lt_trichotomy (q.1 0) 0 with h | h | h
  · simp [scalarRescaled, h, not_lt.mpr h.le]
  · simp [scalarRescaled, h]
  · simp [scalarRescaled, h, not_lt.mpr h.le]

/-- Off-axis continuity follows from continuity of the similarity function. -/
theorem scalarRescaled_continuousAt_off_axis (hf : Continuous f)
    (q : XV 1) (hx : q.1 0 ≠ 0) : ContinuousAt (scalarRescaled f beta) q := by
  have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
  have hpos (z : XV 1) (hz : 0 < z.1 0) : ContinuousAt (scalarRescaled f beta) z := by
    have hp (a : ℝ) : ContinuousAt (fun q : XV 1 => Real.rpow (q.1 0) a) z :=
      (Real.continuousAt_rpow_const _ a (Or.inl hz.ne')).comp'
        (f := fun q : XV 1 => q.1 0) (hX.continuousAt (x := z))
    have hs : ContinuousAt (fun q : XV 1 => scalarSimilarity (q.1 0) (q.2 0)) z :=
      hV.continuousAt.neg.div (hp _) (Real.rpow_pos_of_pos hz _).ne'
    apply ((hp (beta / 3)).mul (hf.continuousAt.comp' hs)).congr_of_eventuallyEq
    filter_upwards [hX.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hz)] with q hq
    simp only [scalarRescaled, if_pos (show 0 < q.1 0 from hq), Pi.mul_apply]
  rcases lt_or_gt_of_ne hx with hn | hp
  · simpa only [Function.comp_def, scalarRescaled_neg] using
      (hpos (-q) (neg_pos.mpr hn)).comp (continuous_neg.continuousAt (x := q))
  · exact hpos q hp

/-- The reflected rescaling is bounded near nonzero position-axis points. -/
theorem scalarRescaled_isBigO_axis
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (q : XV 1) (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
    IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
  have hp := scalarAxis_tendsto_coordinates (s := scalarPositionPositive) hx
  have hn := scalarAxis_tendsto_coordinates (s := scalarPositionNegative) hx
  rw [scalar_axis_nhds, isBigO_sup, isBigO_sup]
  constructor
  · constructor
    · have hh := scalar_scaled_tail_bounded (𝓝[scalarPositionPositive] q) f beta ht hb
        (fun z => z.1 0) (fun z => z.2 0) (q.2 0) hv
        hp.1 self_mem_nhdsWithin hp.2
      apply hh.congr' _ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarRescaled, show 0 < z.1 0 from hz, ↓reduceIte]
    · have hh := scalar_scaled_tail_bounded (𝓝[scalarPositionNegative] q) f beta ht hb
        (fun z => -z.1 0) (fun z => -z.2 0) (-q.2 0) (neg_ne_zero.mpr hv)
        (by simpa only [neg_zero] using hn.1.neg)
        (by filter_upwards [self_mem_nhdsWithin] with z hz; exact neg_pos.mpr hz) hn.2.neg
      apply hh.congr' _ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarRescaled, not_lt.mpr (show z.1 0 < 0 from hz).le,
        show z.1 0 < 0 from hz, ↓reduceIte]
  · apply (isBigO_zero (fun _ : XV 1 => (1 : ℝ)) (𝓝[scalarPositionAxis] q)).congr' _ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [scalarRescaled, show z.1 0 = 0 from hz, lt_self_iff_false, ↓reduceIte]

end

section
variable (f : ℝ → ℝ) (beta : ℝ) (hf : Continuous f)
  (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
  (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
include hf ht hb

/-- The rescaled function is locally bounded away from the origin. -/
theorem scalarRescaled_locally_bounded (q : XV 1) (hq : q ≠ 0) :
    ∃ M : ℝ, ∀ᶠ z in 𝓝 q, |scalarRescaled f beta z| ≤ M := by
  have hh : IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
    by_cases hx : q.1 0 = 0
    · have hv : q.2 0 ≠ 0 := fun hv => hq
        (Prod.ext (scalarCoordinate_eq_zero_iff.mp hx) (scalarCoordinate_eq_zero_iff.mp hv))
      exact scalarRescaled_isBigO_axis f beta ht hb q hx hv
    · exact isBigO_const_of_tendsto
        (scalarRescaled_continuousAt_off_axis f beta hf q hx).tendsto one_ne_zero
  obtain ⟨M, hM⟩ := hh.bound
  refine ⟨M, ?_⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hM

/-- Every compact set away from the origin has a uniform rescaled-tail bound. -/
theorem scalarRescaled_compact_bound
    (K : Set (XV 1)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K, |scalarRescaled f beta q| ≤ M := by
  classical
  have hKnz (q : K) : (q : XV 1) ≠ 0 := by
    intro hq
    exact hz (hq ▸ q.2)
  choose M hM using fun q : K => scalarRescaled_locally_bounded f beta hf ht hb q (hKnz q)
  let U : ∀ q ∈ K, Set (XV 1) := fun q hq => {z | |scalarRescaled f beta z| ≤ M ⟨q, hq⟩}
  obtain ⟨J, hJ⟩ := hK.elim_nhds_subcover' U (fun q hq => hM ⟨q, hq⟩)
  refine ⟨∑ j ∈ J, |M j|, ?_⟩
  intro q hq
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hJ hq)
  have hh := hqp
  exact hh.trans ((le_abs_self (M p)).trans (Finset.single_le_sum
    (fun j _ => abs_nonneg (M j)) hp))

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
