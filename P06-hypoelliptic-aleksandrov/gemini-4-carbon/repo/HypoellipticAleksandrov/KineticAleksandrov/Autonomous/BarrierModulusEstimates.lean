module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionContinuous
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionSlices
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Gauge below one implies product norm at most one, using both kinetic weights. -/
theorem barrier_small_gauge_norm {q : ℝ × ℝ} (hq : bellmanGauge q < 1) : ‖q‖ ≤ 1 := by
  obtain ⟨hX, hv⟩ := bellmanGauge_coordinate_bounds q
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpow : bellmanGauge q ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ (bellmanGauge_nonneg q) hq.le 3
  exact ⟨hX.trans hpow, hv.trans hq.le⟩

/-- A reference-scale axis increment is controlled either by distant jets or a compact ball. -/
theorem barrier_reference_axis_increment (Phi : (ℝ × ℝ) → ℝ)
    (axis : ℝ → ℝ × ℝ)
    (haxisdist : ∀ t u, ‖axis t - axis u‖ ≤ |t - u|)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hball : ∀ q, ‖q‖ ≤ 2 → |Phi q| ≤ B)
    (hderiv : ∀ t, 1 ≤ bellmanGauge (axis t) →
      ∃ g : ℝ, HasDerivAt (Phi ∘ axis) g t ∧ |g| ≤ D)
    (x y : ℝ) (hxy : |y - x| ≤ 1) : |Phi (axis y) - Phi (axis x)| ≤ D + 2 * B := by
  by_cases hfar : ∀ t ∈ uIcc x y, 1 ≤ bellmanGauge (axis t)
  · have hd (t : ℝ) (ht : t ∈ uIcc x y) := hderiv t (hfar t ht)
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).choose_spec.1.differentiableAt)
      (fun t ht => by
        rw [(hd t ht).choose_spec.1.deriv, Real.norm_eq_abs]
        exact (hd t ht).choose_spec.2)
      (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left hxy hD)).trans
      (by simpa only [mul_one] using le_add_of_nonneg_right (mul_nonneg (by norm_num) hB))
  · push Not at hfar
    obtain ⟨t, ht, htg⟩ := hfar
    have htq := barrier_small_gauge_norm htg
    have hx : ‖axis x‖ ≤ 2 := by
      linarith only [(haxisdist x t).trans (by simpa only [abs_sub_comm] using (abs_sub_left_of_mem_uIcc ht).trans hxy), (norm_le_norm_add_norm_sub' (axis x) (axis t)), htq]
    have hy : ‖axis y‖ ≤ 2 := by
      linarith only [(haxisdist y t).trans ((abs_sub_right_of_mem_uIcc ht).trans hxy), (norm_le_norm_add_norm_sub' (axis y) (axis t)), htq]
    exact (abs_sub _ _).trans (by linarith only [hball _ hx, hball _ hy, hD])


/-- Off the origin the extension has the original local germ. -/
theorem barrierExtension_eventuallyEq (phi : (ℝ × ℝ) → ℝ) {q : ℝ × ℝ}
    (hq : q ≠ (0, 0)) : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact bellmanOriginExtension_eqOn phi hz

/-- A gauge at least one excludes the origin. -/
theorem barrier_gauge_one_ne_zero {q : ℝ × ℝ} (hq : 1 ≤ bellmanGauge q) : q ≠ (0, 0) := by
  intro he
  subst q
  norm_num [bellmanGauge, bellmanGaugePower] at hq




/-- Recover a point from its positive-radius kinetic normalization. -/
theorem barrier_normalized_point (r : ℝ) (hr : 0 < r) (x v : ℝ) :
    bellmanPlaneDilation r (x / r ^ 3, v / r) = (x, v) := by
  simp only [bellmanPlaneDilation]
  congr 1 <;> field_simp



/-- The actual extended Bellman witness has the source modulus without a new analytic premise. -/
theorem barrier_coordinate_modulus {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z w : ℝ × ℝ,
      |bellmanOriginExtension phi z - bellmanOriginExtension phi w| ≤
        D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)     := by
  have barrierExtension_scaling (r : ℝ) (hr : 0 < r) (q : ℝ × ℝ) :
      bellmanOriginExtension phi (bellmanPlaneDilation r q) =
      r ^ alpha * bellmanOriginExtension phi q := by
    by_cases hq : q = (0, 0)
    · subst q
      simp [bellmanPlaneDilation, bellmanOriginExtension_zero]
    · rw [bellmanOriginExtension_eqOn phi (bellmanPlaneDilation_ne_zero r hr q hq),
        bellmanOriginExtension_eqOn phi hq]
      exact h.2 r hr q hq
  have barrier_velocity_increment (D : ℝ) (hb : ∀ x y X : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (X, y) - bellmanOriginExtension phi (X, x)| ≤ D) (x : ℝ) (y : ℝ) (X : ℝ) :
      |bellmanOriginExtension phi (X, y) - bellmanOriginExtension phi (X, x)| ≤
      D * |y - x| ^ alpha := by
    by_cases hxy : y = x
    · subst y
      rw [sub_self, abs_zero]
      exact mul_nonneg (le_trans (abs_nonneg _) (hb x x X (by simp)))
        (Real.rpow_nonneg (abs_nonneg _) _)
    let r := |y - x|
    have hr := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hn : |y / r - x / r| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hr]
      exact le_of_eq (div_self hr.ne')
    have hh := hb (x / r) (y / r) (X / r ^ 3) hn
    have hx := barrierExtension_scaling r hr (X / r ^ 3, x / r)
    have hy := barrierExtension_scaling r hr (X / r ^ 3, y / r)
    rw [barrier_normalized_point r hr] at hx hy
    rw [hy, hx, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr alpha)]
    exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)).trans_eq (mul_comm _ _)
  have barrier_position_increment (D : ℝ) (hb : ∀ x y v : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤ D) (x : ℝ) (y : ℝ) (v : ℝ) :
      |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤
      D * |y - x| ^ (alpha / 3) := by
    by_cases hxy : y = x
    · subst y
      rw [sub_self, abs_zero]
      exact mul_nonneg (le_trans (abs_nonneg _) (hb x x v (by simp)))
        (Real.rpow_nonneg (abs_nonneg _) _)
    let r := |y - x| ^ (1 / 3 : ℝ)
    have hdiff := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hr : 0 < r := Real.rpow_pos_of_pos hdiff _
    have hr3 : r ^ 3 = |y - x| := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdiff.le]
      norm_num
    have hn : |y / r ^ 3 - x / r ^ 3| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos (pow_pos hr _), hr3, div_self hdiff.ne']
    have hh := hb (x / r ^ 3) (y / r ^ 3) (v / r) hn
    have hx := barrierExtension_scaling r hr (x / r ^ 3, v / r)
    have hy := barrierExtension_scaling r hr (y / r ^ 3, v / r)
    rw [barrier_normalized_point r hr] at hx hy
    rw [hy, hx, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr alpha)]
    have hpower : r ^ alpha = |y - x| ^ (alpha / 3) := by
      rw [← Real.rpow_mul hdiff.le]
      congr 1
      ring
    exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)).trans_eq
      (by rw [hpower, mul_comm])
  have barrier_reference_increments :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ x y v : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤ D ∧
      |bellmanOriginExtension phi (v, y) - bellmanOriginExtension phi (v, x)| ≤ D := by
    obtain ⟨_, hX, hv, _⟩ := h.origin_jet_bounds
    obtain ⟨CX, hCX, hbX⟩ := hX
    obtain ⟨Cv, hCv, hbv⟩ := hv
    have hψ := h.origin_extension_continuous ha
    obtain ⟨B, hBb⟩ :=
      (isCompact_closedBall 0 2).exists_bound_of_continuousOn hψ.continuousOn
    let B' := max B 0
    have hB : 0 ≤ B' := le_max_right _ _
    have hball q (hq : ‖q‖ ≤ 2) : |bellmanOriginExtension phi q| ≤ B' :=
      (by
        have hh := hBb q (by simpa using hq)
        rw [Real.norm_eq_abs] at hh
        exact hh.trans (le_max_left _ _))
    refine ⟨CX + Cv + 2 * B', by positivity, fun x y v hxy => ?_⟩
    constructor
    · have hh := barrier_reference_axis_increment (bellmanOriginExtension phi)
        (fun t => (t, v)) (fun t u => by
          simp only [Prod.mk_sub_mk, sub_self,
          Prod.norm_def, Real.norm_eq_abs, norm_zero]
          exact max_le le_rfl (abs_nonneg (t - u)))
        CX B' hCX hB hball (fun t ht => ?_) x y hxy
      · exact hh.trans (by linarith only [hCv])
      · have hq := barrier_gauge_one_ne_zero ht
        have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
          (by norm_num)
        have he := (barrierExtension_eventuallyEq phi hq).comp_tendsto
          ((continuous_id.prodMk continuous_const).tendsto t)
        refine ⟨bellmanDx phi (t, v), (bellman_hasDerivAt_first hd).congr_of_eventuallyEq he, ?_⟩
        exact (hbX _ hq).trans (by
          have hh := Real.rpow_le_rpow_of_nonpos zero_lt_one ht (by linarith : alpha - 3 ≤ 0)
          simpa using mul_le_mul_of_nonneg_left hh hCX)
    · have hh := barrier_reference_axis_increment (bellmanOriginExtension phi)
        (fun t => (v, t)) (fun t u => by
          simp only [Prod.mk_sub_mk, sub_self,
          Prod.norm_def, Real.norm_eq_abs, norm_zero]
          exact max_le (abs_nonneg (t - u)) le_rfl)
        Cv B' hCv hB hball (fun t ht => ?_) x y hxy
      · exact hh.trans (by linarith only [hCX])
      · have hq := barrier_gauge_one_ne_zero ht
        have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
          (by norm_num)
        have he := (barrierExtension_eventuallyEq phi hq).comp_tendsto
          ((continuous_const.prodMk continuous_id).tendsto t)
        refine ⟨bellmanDv phi (v, t), (bellman_hasDerivAt_second hd).congr_of_eventuallyEq he, ?_⟩
        exact (hbv _ hq).trans (by
          have hh := Real.rpow_le_rpow_of_nonpos zero_lt_one ht (by linarith : alpha - 1 ≤ 0)
          simpa using mul_le_mul_of_nonneg_left hh hCv)
  obtain ⟨D, hD, hb⟩ := barrier_reference_increments
  refine ⟨D, hD, fun z w => ?_⟩
  exact (abs_sub_le (bellmanOriginExtension phi z) (bellmanOriginExtension phi (w.1, z.2)) (bellmanOriginExtension phi w)).trans (by simpa only [mul_add] using add_le_add (barrier_position_increment D (fun x y v hh => (hb x y v hh).1) w.1 z.1 z.2) (barrier_velocity_increment D (fun x y X hh => (hb x y X hh).2) w.2 z.2 w.1))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization

