module
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrierCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionContinuous
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierLowerBound
import Mathlib

/-! # Flattening a homogeneous Bellman barrier near its pole

Scaling the flattened function back gives classical exterior tests. Two such tests with
the same pole agree outside a compact set. All losses from flattening occur in a box
of position width `O(s³)` and velocity width `O(s)`.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
open Set Filter Metric
open scoped Topology

structure Exterior (lam Lam α : ℝ) where
  profile : ℝ → Z → ℝ
  large : Z → ℝ
  cost : ℝ
  pos : ℝ
  cost_nonneg : 0 ≤ cost
  positive : 0 < pos
  regular : ∀ s > (0:ℝ), C2 (profile s)
  compact : ∀ s > (0:ℝ), HasCompactSupport (profile s - large)
  size : ∀ s > (0:ℝ), ∀ q, |profile s q-large q| ≤ cost*s^α
  bound : ∀ s > (0:ℝ), ∀ b ∈ Icc lam Lam, ∀ q, |P b (profile s) q| ≤ cost * s^(α-2)
  good : ∀ s > (0:ℝ), ∀ b ∈ Icc lam Lam, ∀ q : Z, ¬(|q.1| ≤ 2*s^3 ∧ |q.2| ≤ 2*s) →
    pos * bellmanGauge q ^ (α-2) ≤ P b (profile s) q

private def flat (φ : Z → ℝ) (q : Z) := Real.smoothTransition (bellmanGaugePower q - 1) * φ q
private lemma flat_far (φ : Z → ℝ) {q} (hq : 2 < bellmanGaugePower q) : flat φ =ᶠ[𝓝 q] φ :=
  (bellmanGaugePower_continuous.continuousAt.eventually_const_lt hq).mono fun z hz => by simp [flat,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ bellmanGaugePower z-1)]

private lemma smooth_flat {α : ℝ} {φ : Z → ℝ} (h : IsBellmanHomogeneous α φ) : C2 (flat φ) := by
  apply contDiff_iff_contDiffAt.mpr; intro z
  by_cases hz : z = 0
  · subst z
    have e : flat φ =ᶠ[𝓝 0] fun _ => 0 :=
      (bellmanGaugePower_continuous.continuousAt.eventually_lt continuousAt_const (show bellmanGaugePower 0 < 1 by norm_num [bellmanGaugePower])).mono fun y hy => by simp [flat,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy.le)]
    exact contDiffAt_const.congr_of_eventuallyEq e
  · exact ((Real.smoothTransition.contDiff.comp (bellmanGaugePower_contDiff.of_le (by simp) |>.sub contDiff_const)).contDiffAt).mul
      (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hz))

private lemma large_eq {α} {φ : Z → ℝ} (h : IsBellmanHomogeneous α φ) {r : ℝ} (hr : 0 < r) (z : Z) :
    resize (r^α) r 0 (bellmanOriginExtension φ) z = bellmanOriginExtension φ z := by
  by_cases hz : z = 0
  · subst z; simp [resize,coord,bellmanOriginExtension,show (0 : Z) = (0,0) from rfl]
  · have hz' := bellmanPlaneDilation_ne_zero r⁻¹ (inv_pos.mpr hr) z hz
    change r^α * bellmanOriginExtension φ ((r⁻¹)^3*(z.1-0), r⁻¹*z.2) = _
    rw [sub_zero]; change r^α * bellmanOriginExtension φ (bellmanPlaneDilation r⁻¹ z) = _
    rw [bellmanOriginExtension_eqOn φ hz',h.2 _ (inv_pos.mpr hr) _ hz,← mul_assoc, Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne',one_mul,bellmanOriginExtension_eqOn φ hz]

private lemma compact_error {φ : Z → ℝ} : HasCompactSupport (flat φ - bellmanOriginExtension φ) := by
  have hk := bellmanGaugePower_sublevel_isCompact 2 (by norm_num)
  apply HasCompactSupport.of_support_subset_isCompact hk
  intro q hq; by_contra h
  change ¬ bellmanGaugePower q ≤ 2 at h
  have gt := lt_of_not_ge h
  have qne : q ≠ 0 := by rintro rfl; norm_num [bellmanGaugePower] at gt
  exact hq (sub_eq_zero.mpr ((flat_far φ gt).eq_of_nhds.trans (bellmanOriginExtension_eqOn φ qne).symm))

private lemma scale_op {α s b : ℝ} (hs : 0 < s) (g : Z → ℝ) (q : Z) :
    P b (resize (s^α) s 0 g) q = s^(α-2) * P b g (coord s 0 q) := by rw [P_resize _ _ _ _ _ hs,Real.rpow_sub hs]; norm_num

private lemma outside {s : ℝ} (hs : 0 < s) {q : Z} (hq : ¬ (|q.1| ≤ 2*s^3 ∧ |q.2| ≤ 2*s)) : 2 < bellmanGaugePower (coord s 0 q) := by
  let y := coord s 0 q
  by_contra! h
  have e1 : q.1 = s^3 * y.1 := by simp [y,coord,hs.ne']
  have e2 : q.2 = s*y.2 := by simp [y,coord,hs.ne']
  change y.1^2 + y.2^6 ≤ 2 at h
  have hx : |y.1| ≤ 2 := abs_le.mpr ⟨by nlinarith [Even.pow_nonneg (by decide : Even 6) y.2],by nlinarith [Even.pow_nonneg (by decide : Even 6) y.2]⟩
  have hv : |y.2| ≤ 2 := by
    by_contra! hv
    have hh := pow_le_pow_left₀ (by norm_num : 0 ≤ (2:ℝ)) hv.le 6
    rw [pow_abs,abs_of_nonneg (Even.pow_nonneg (by decide : Even 6) _)] at hh; nlinarith [sq_nonneg y.1]
  apply hq; rw [e1,e2,abs_mul,abs_mul,abs_of_pos (pow_pos hs _),abs_of_pos hs]; constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx (pow_pos hs 3).le, mul_le_mul_of_nonneg_left hv hs.le]

theorem exterior {lam Lam α c : ℝ} {φ : Z → ℝ} (h : IsBellmanHomogeneous α φ) (hα : 0 < α) (ha : α < 1) (hc : 0 < c)
    (he : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam, c * bellmanGauge q ^ (α-2) ≤ bellmanOperator b φ q) : Nonempty (Exterior lam Lam α) := by
  classical
  let g := flat φ
  have hg := smooth_flat h
  let E := bellmanOriginExtension φ
  have hs (s : ℝ) : 0 < s → resize (s^α) s 0 E = E := fun h => funext (large_eq ‹IsBellmanHomogeneous α φ› h)
  have cErr := compact_error (φ := φ)
  obtain ⟨D,hD⟩ := cErr.exists_bound_of_continuous (hg.continuous.sub (h.origin_extension_continuous hα))
  obtain ⟨C₀,h0⟩ := ((bellmanGaugePower_sublevel_isCompact 2 (by norm_num)).prod (isCompact_Icc (a := lam) (b := Lam))).exists_bound_of_continuousOn (continuous_P hg).continuousOn
  obtain ⟨C₁,h1⟩ := isCompact_univ.exists_bound_of_continuousOn (h.image_continuous (lam := lam) (Lam := Lam)).continuousOn
  let C := max D (max C₀ C₁)
  have C0 : 0 ≤ C := ((norm_nonneg _).trans (hD 0)).trans (le_max_left ..)
  refine ⟨⟨fun s => resize (s^α) s 0 g,E,C,c,C0,hc,fun s _ => smooth_resize hg ..,?_,?_,?_,?_⟩⟩
  · intro s ht; rw [← hs s ht]
    convert compact_resize cErr (s^α) s 0 ht using 1
    funext z; exact (mul_sub ..).symm
  · intro s ht q; rw [← congrFun (hs s ht) q]
    change |s^α*g _ - s^α*E _| ≤ _; rw [← mul_sub,abs_mul,abs_of_pos (Real.rpow_pos_of_pos ht _),mul_comm]
    exact mul_le_mul_of_nonneg_right ((hD _).trans (le_max_left ..)) (Real.rpow_nonneg ht.le _)
  · intro s ht b hb q; rw [scale_op ht,abs_mul,abs_of_pos (Real.rpow_pos_of_pos ht _),mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    let y := coord s 0 q
    by_cases hy : bellmanGaugePower y ≤ 2
    · exact (h0 (y,b) ⟨hy,hb⟩).trans ((le_max_left ..).trans (le_max_right ..))
    · have gt := lt_of_not_ge hy
      have yne : y ≠ 0 := by rintro e; norm_num [e,bellmanGaugePower] at gt
      let w := bellmanSpherePoint y yne
      let ρ := bellmanGauge y
      have hp := bellmanGauge_pos y yne
      have hr : 1 ≤ ρ := by by_contra! lt; have H := pow_le_pow_left₀ hp.le lt.le 6; simpa [ρ,bellmanGauge_pow_six] using (not_le.mpr (by linarith : 1 < bellmanGaugePower y) (by simpa [ρ,bellmanGauge_pow_six] using H))
      have hh := bellman_homogeneous_operator_scaling h ρ hp w.val w.ne_zero b
      rw [show bellmanPlaneDilation ρ w.val = y from bellmanSpherePoint_reconstruct ..] at hh
      rw [show P b g (coord s 0 q) = bellmanOperator b φ y from (physical_eq_bellman hg _ _).trans (bellman_operator_germ_eq (flat_far _ gt) b),hh,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hp _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith))).trans ((h1 (w,⟨b,hb⟩) trivial).trans ((le_max_right ..).trans (le_max_right ..)))
  · intro s ht b hb q hq
    let y := coord s 0 q
    have gt := outside ht hq
    have yne : y ≠ 0 := by intro e; change 2 < bellmanGaugePower y at gt; norm_num [e,bellmanGaugePower] at gt
    have qe : bellmanPlaneDilation s y = q := by ext <;> simp [y,coord,bellmanPlaneDilation,ht.ne']
    have eq := bellman_homogeneous_operator_scaling h s ht y yne b
    rw [qe] at eq
    exact (he _ (qe ▸ bellmanPlaneDilation_ne_zero s ht y yne) _ hb).trans_eq (eq.trans (by rw [scale_op ht,physical_eq_bellman hg,bellman_operator_germ_eq (flat_far φ gt)]))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
