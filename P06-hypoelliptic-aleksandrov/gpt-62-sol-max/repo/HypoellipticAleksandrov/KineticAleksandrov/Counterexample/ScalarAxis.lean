module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAnsatz
import Mathlib.Tactic

/-!
# Joint limits at the scalar position axis

The matching equation makes the two similarity tails converge to the same axis trace.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology

/-- Three position sectors used to approach the axis. -/
abbrev scalarPositionPositive : Set (XV 1) := {z | 0 < z.1 0}
abbrev scalarPositionNegative : Set (XV 1) := {z | z.1 0 < 0}
abbrev scalarPositionAxis : Set (XV 1) := {z | z.1 0 = 0}

theorem scalar_axis_nhds (q : XV 1) :
    𝓝 q = 𝓝[scalarPositionPositive] q ⊔ 𝓝[scalarPositionNegative] q ⊔ 𝓝[scalarPositionAxis] q := by
  have h : scalarPositionPositive ∪ scalarPositionNegative ∪ scalarPositionAxis = univ := by
    ext z
    simp only [scalarPositionPositive, scalarPositionNegative, scalarPositionAxis,
      mem_union, mem_setOf_eq, mem_univ, iff_true]
    rcases lt_trichotomy (z.1 0) 0 with hz | hz | hz <;> tauto
  rw [← nhdsWithin_union, ← nhdsWithin_union, h, nhdsWithin_univ]

theorem scalarAxis_tendsto_coordinates {q : XV 1} {s : Set (XV 1)} (hx : q.1 0 = 0) :
    Tendsto (fun z => z.1 0) (𝓝[s] q) (𝓝 0) ∧
      Tendsto (fun z => z.2 0) (𝓝[s] q) (𝓝 (q.2 0)) := by
  have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
  exact ⟨hx ▸ (hX.tendsto q).mono_left nhdsWithin_le_nhds,
    (hV.tendsto q).mono_left nhdsWithin_le_nhds⟩

/-- Exact power cancellation for every real jet degree, including negative degrees. -/
theorem scalar_similarity_power_cancel_general (beta x v : ℝ) (hx : 0 < x) :
    Real.rpow x (beta / 3) * Real.rpow |scalarSimilarity x v| beta = Real.rpow |v| beta := by
  simp only [scalarSimilarity, Real.rpow_eq_pow, abs_div, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hx (1 / 3 : ℝ))]
  rw [Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul hx.le, show (1 / 3 : ℝ) * beta = beta / 3 by ring]
  field_simp

/-- Specialization to the degree of the undifferentiated profile. -/
theorem scalar_similarity_power_cancel (gamma : ScalarGamma) (x v : ℝ) (hx : 0 < x) :
    Real.rpow x gamma.1 * Real.rpow |scalarSimilarity x v| (3 * gamma.1) =
      Real.rpow |v| (3 * gamma.1) := by
  simpa only [show 3 * gamma.1 / 3 = gamma.1 by ring] using
    scalar_similarity_power_cancel_general (3 * gamma.1) x v hx

/-- The ansatz equals its normalized tail times the velocity leading power. -/
theorem scalarAnsatz_normalized (gamma : ScalarGamma) (Lam x v : ℝ)
    (hx : 0 < x) (hv : v ≠ 0) :
    scalarAnsatz gamma Lam x v = Real.rpow |v| (3 * gamma.1) *
      (F gamma Lam (scalarSimilarity x v) /
        Real.rpow |scalarSimilarity x v| (3 * gamma.1)) := by
  have hs : scalarSimilarity x v ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hv) (Real.rpow_pos_of_pos hx (1 / 3 : ℝ)).ne'
  have hp := (Real.rpow_pos_of_pos (abs_pos.mpr hs) (3 * gamma.1)).ne'
  rw [← scalar_similarity_power_cancel gamma x v hx]
  unfold scalarAnsatz scalarSimilarity
  unfold scalarSimilarity at hp
  simp only [Real.rpow_eq_pow, neg_div] at hp ⊢
  field_simp

/-- The signed similarity coordinate tends to the appropriate infinite ray in a joint axis limit. -/
theorem scalarSimilarity_tendsto_axis {ι : Type*} (l : Filter ι) (X V : ι → ℝ)
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

/-- Joint approach from positive positions gives the prescribed nonzero-velocity trace. -/
theorem scalarAnsatz_tendsto_axis {ι : Type*} (l : Filter ι)
    (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (X V : ι → ℝ) (v : ℝ) (hv : v ≠ 0)
    (hX : Tendsto X l (𝓝 0)) (hXp : ∀ᶠ i in l, 0 < X i)
    (hV : Tendsto V l (𝓝 v)) :
    Tendsto (fun i => scalarAnsatz gamma Lam (X i) (V i)) l
      (𝓝 (scalarTrace gamma Lam v)) := by
  have hS := scalarSimilarity_tendsto_axis l X V v hv hX hXp hV
  have hRatio : Tendsto (fun i =>
      F gamma Lam (scalarSimilarity (X i) (V i)) /
        Real.rpow |scalarSimilarity (X i) (V i)| (3 * gamma.1)) l
      (𝓝 (Real.rpow (9 * Lam) (-gamma.1))) := by
    by_cases hvn : v < 0
    · rw [ite_eq_left hvn] at hS
      exact (F_ratio_atTop gamma Lam hLam).comp hS
    · rw [ite_eq_right hvn] at hS
      exact (F_ratio_atBot gamma Lam hLam hmatch).comp hS
  have hPow : Tendsto (fun i => Real.rpow |V i| (3 * gamma.1)) l
      (𝓝 (Real.rpow |v| (3 * gamma.1))) := by
    have hp : 0 ≤ 3 * gamma.1 := (mul_pos (by norm_num) gamma.2.1).le
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      ((Real.continuous_rpow_const hp).tendsto |v|).comp hV.abs
  have h := hRatio.mul hPow
  change Tendsto _ l (𝓝 (scalarTrace gamma Lam v)) at h
  apply h.congr'
  filter_upwards [hXp, hV.eventually_ne hv] with i hi hvi
  rw [scalarAnsatz_normalized gamma Lam (X i) (V i) hi hvi]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
