module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic
public import RequestProject.BZLevel
public import RequestProject.SmoothDomain
public import RequestProject.Transport

/-!
# The actual unit disk and its positively oriented boundary

The disk is a smooth domain in the project's graph-chart definition. Its
local graph is constructed from `2y - y² - x² = 0`, and then extended by the
already proved smooth cutoff extension. The standard circle map has all
the fields of `IsBoundaryParam`, including the positive signed-area identity.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Real ContDiff ComplexConjugate

/-- The unit disk has actual globally smooth and Lipschitz local graph charts. -/
theorem isSmoothDomain_unitDisk : IsSmoothDomain (ball 0 1) := by
  refine ⟨⟨isOpen_ball, isConnected_ball (by norm_num)⟩, fun p hp => ?_⟩
  rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hp
  have hp1 : ‖p‖ = 1 := by
    simpa using hp
  obtain ⟨K, F, hFc, hFl, hF0, hFb, hFiff⟩ : ∃ K F, ContDiff ℝ ∞ F ∧ LipschitzWith K F ∧ F 0 = 0 ∧ (∀ x : ℝ, |x| < 1 / 8 → |F x| < 1 / 2) ∧ (∀ x : ℝ, |x| < 1 / 8 → ∀ y : ℝ, |y| < 1 / 2 → (0 < 2 * y - y ^ 2 - x ^ 2 ↔ F x < y)) := by
    let G : ℝ → ℝ → ℝ := fun x y => 2 * y - y ^ 2 - x ^ 2
    obtain ⟨f₀, hf₀, hf₀iff, hf₀c⟩ :=
      exists_level_graph (r₂ := (1 / 4)) (h := (1 / 2))
        (h' := (1 / 4)) (κ := 1) (ε := 0)
        (by
          dsimp only [G]
          fun_prop) (by norm_num) (by norm_num) (by norm_num) (show ∀ x : ℝ, |x| < 1 / 4 → ∀ y₁ y₂ : ℝ, -(1 / 2) < y₁ → y₁ ≤ y₂ → y₂ < 1 / 2 → G x y₁ + 1 * (y₂ - y₁) ≤ G x y₂ by
          intro x _ y₁ y₂ _ hle hhi
          dsimp only [G]
          nlinarith [(mul_nonneg (sub_nonneg.mpr hle) (by linarith) : 0 ≤ (y₂ - y₁) * (1 - y₁ - y₂))]) (show ∀ x : ℝ, |x| < 1 / 4 → G x (-(1 / 4)) < 0 by
          intro x _
          dsimp only [G]
          nlinarith [sq_nonneg x]) (show ∀ x : ℝ, |x| < 1 / 4 → 0 < G x (1 / 4) by
          intro x hx
          dsimp only [G]
          nlinarith [mul_pos (show 0 < x + 1 / 4 by linarith [(abs_lt.mp hx).1]) (show 0 < 1 / 4 - x by linarith [(abs_lt.mp hx).2])])
    obtain ⟨F, hFc, ⟨K, hFl⟩, hFf⟩ :=
      exists_smooth_extension (r := (1 / 8)) (r₂ := (1 / 4))
        (by norm_num) (by norm_num) hf₀c
    refine ⟨K, F, hFc, hFl, ?_, ?_, ?_⟩
    · rw [hFf 0 (by norm_num), show f₀ 0 = 0 by
      obtain ⟨hb, he⟩ := hf₀ 0 (by norm_num)
      have hb' := (abs_lt.mp hb).2
      exact (mul_eq_zero.mp (show f₀ 0 * (2 - f₀ 0) = 0 by
        dsimp only [G] at he
        nlinarith [he])).resolve_right (by linarith)]
    · intro x hx
      rw [hFf x hx.le]
      have hb := (hf₀ x (by linarith : |x| < 1 / 4)).1
      linarith
    · intro x hx y hy
      rw [hFf x hx.le]
      exact hf₀iff x (by linarith : |x| < 1 / 4) y hy
  let c : ℂ := -Complex.I * conj p
  have hc : ‖c‖ = 1 := by simp [c, hp1]
  refine ⟨c, 1 / 8, 1 / 2, K, F, hc, by norm_num, by norm_num,
    hFc, hFl, hF0, hFb, ?_⟩
  intro w hwx hwy
  let q := c * (w - p)
  change |q.re| < (1 / 8) at hwx
  change |q.im| < (1 / 2) at hwy
  change w ∈ ball 0 1 ↔ F q.re < q.im
  rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg w), ← hFiff q.re hwx q.im hwy]
  constructor <;> intro h <;> nlinarith [show ‖w‖ ^ 2 = q.re ^ 2 + (q.im - 1) ^ 2 by
    calc
      _ = _ := by simp [hc]
      _ = Complex.normSq (c * w) := (Complex.normSq_eq_norm_sq _).symm
      _ = q.re ^ 2 + (q.im - 1) ^ 2 := by
        rw [show c * w = q - Complex.I by
          dsimp only [q]
          rw [mul_sub, show c * p = -Complex.I by
            have hpp : conj p * p = 1 := by
              rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hp1]
              norm_num
            dsimp only [c]
            rw [mul_assoc, hpp, mul_one]]
          ring, Complex.normSq_apply]
        simp
        ring]

/-- The disk therefore satisfies the domain hypothesis used by physical Green identities. -/
theorem isLipschitzDomain_unitDisk : IsLipschitzDomain (ball 0 1) :=
  isSmoothDomain_unitDisk.isLipschitzDomain

theorem unitDisk_bounded : Bornology.IsBounded (ball (0 : ℂ) 1) :=
  Metric.isBounded_ball

/-- The standard positively oriented circle is a genuine boundary parameter for the disk. -/
theorem unitCircle_isBoundaryParam :
    IsBoundaryParam (ball 0 1) (circleMap 0 1) := by
  refine
    { lipschitz := ⟨Real.nnabs 1, lipschitzWith_circleMap 0 1⟩
      periodic := periodic_circleMap 0 1
      injOn := injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1)
        (a := 0) (b := 2 * π) (by norm_num) (by linarith)
      image := ?_
      const_speed := ?_
      area := ?_ }
  · rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply Subset.antisymm
    · rintro w ⟨θ, _, rfl⟩
      exact circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ
    · intro w hw
      exact (image_mono Ioc_subset_Icc_self) (by
        simpa using hw)
  · refine ⟨1, by norm_num, ae_of_all _ fun θ => ?_⟩
    simp
  · have him : ∀ θ : ℝ,
        (conj (circleMap 0 1 θ) * deriv (circleMap 0 1) θ).im = 1 := by
      intro θ
      rw [deriv_circleMap, ← mul_assoc, show conj (circleMap 0 1 θ) * circleMap 0 1 θ = 1 by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        simp]
      simp
    simp_rw [him]
    rw [intervalIntegral.integral_const, show (volume (ball (0 : ℂ) 1)).toReal = π by
      simp]
    simp

end PolyaNeumann

end
