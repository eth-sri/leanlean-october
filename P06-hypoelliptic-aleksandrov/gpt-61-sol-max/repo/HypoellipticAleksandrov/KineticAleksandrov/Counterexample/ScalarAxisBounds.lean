module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarDerivativeGrowth
import Mathlib.Tactic

/-! # Scaled similarity tails stay bounded at every nonzero position-axis point -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics
open scoped Topology

/-- Exact power cancellation for every real jet degree, including negative degrees. -/
theorem scalar_similarity_power_cancel_general (beta x v : ℝ) (hx : 0 < x) :
    Real.rpow x (beta / 3) * Real.rpow |scalarSimilarity x v| beta = Real.rpow |v| beta := by
  simp only [scalarSimilarity, Real.rpow_eq_pow, abs_div, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hx (1 / 3 : ℝ))]
  rw [Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul hx.le, show (1 / 3 : ℝ) * beta = beta / 3 by ring]
  have hp := (Real.rpow_pos_of_pos hx (beta / 3)).ne'
  field_simp

variable {ι : Type*} (l : Filter ι)

/-- The signed similarity coordinate tends to the appropriate infinite ray in a joint axis limit. -/
theorem scalarSimilarity_tendsto_axis  (X V : ι → ℝ)
    (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    Tendsto (fun i => scalarSimilarity (X i) (V i)) l
      (if v < 0 then atTop else atBot) := by
  have hK : Tendsto (fun i => Real.rpow (X i) (1 / 3)) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 3 : ℝ))).tendsto 0
      simpa only [Real.rpow_eq_pow, Function.comp_def,
        Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using h.comp hX
    · filter_upwards [hXp] with i hi
      exact Real.rpow_pos_of_pos hi _
  have hInv := hK.inv_tendsto_nhdsGT_zero
  rcases lt_or_gt_of_ne hv with hv | hv
  · rw [ite_eq_left hv]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.pos_mul_atTop (neg_pos.mpr hv) hInv
  · rw [ite_eq_right (not_lt.mpr hv.le)]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.neg_mul_atTop (neg_neg_of_pos hv) hInv

/-- Two actual similarity-tail bounds give local boundedness after kinetic rescaling at an axis. -/
theorem scalar_scaled_tail_bounded  (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (X V : ι → ℝ) (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    IsBigO l (fun i => Real.rpow (X i) (beta / 3) * f (scalarSimilarity (X i) (V i)))
      (fun _ => (1 : ℝ)) := (IsBigO.trans
  (IsBigO.congr'
    (IsBigO.mul (isBigO_refl (fun i => (X i).rpow (beta / 3)) l)
      (if hvn : v < 0 then
        IsBigO.comp_tendsto ht
          (Eq.mp (congrArg (fun _a => Tendsto (fun i => scalarSimilarity (X i) (V i)) l _a) (ite_eq_left hvn))
            (scalarSimilarity_tendsto_axis l X V v hv hX hXp hV))
      else
        IsBigO.comp_tendsto hb
          (Eq.mp (congrArg (fun _a => Tendsto (fun i => scalarSimilarity (X i) (V i)) l _a) (ite_eq_right hvn))
            (scalarSimilarity_tendsto_axis l X V v hv hX hXp hV))))
    EventuallyEq.rfl
    (mp_mem hXp (univ_mem' (id fun i hi => scalar_similarity_power_cancel_general beta (X i) (V i) hi))))
  (isBigO_const_of_tendsto
    (id
      (Tendsto.comp (ContinuousAt.tendsto (Real.continuousAt_rpow_const |v| beta (Or.inl (abs_ne_zero.mpr hv))))
        (Tendsto.abs hV)))
    one_ne_zero))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
