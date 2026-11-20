module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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

private lemma exists_unitDisk_graph :
    ∃ (K : NNReal) (F : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) F ∧ LipschitzWith K F ∧
      F 0 = 0 ∧
      (∀ x : ℝ, |x| < 1 / 8 → |F x| < 1 / 2) ∧
      (∀ x : ℝ, |x| < 1 / 8 → ∀ y : ℝ, |y| < 1 / 2 →
        (0 < 2 * y - y ^ 2 - x ^ 2 ↔ F x < y)) := by
  let f (x : ℝ) := 1 - Real.sqrt (1 - x ^ 2)
  have hx2 (x : ℝ) (hx : |x| < 1 / 4) : x ^ 2 < 1 / 16 := by
    nlinarith [mul_pos (show 0 < 1 / 4 - x by grind)
      (show 0 < 1 / 4 + x by grind)]
  obtain ⟨F, hFc, ⟨K, hFl⟩, hFf⟩ := exists_smooth_extension (f₀ := f)
    (r := (1 / 8 : ℝ)) (r₂ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    (fun x hx => contDiffAt_const.sub ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt
      (by grind)))
  refine ⟨K, F, hFc, hFl, ?_, ?_, ?_⟩
  grind
  · intro x hx
    have h := hx2 x (by linarith)
    have hs := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
      (show (1 / 2 : ℝ) ^ 2 < 1 - x ^ 2 by linarith)
    have ht := (Real.sqrt_le_left zero_le_one).mpr (show 1 - x ^ 2 ≤ 1 ^ 2 by nlinarith)
    rw [hFf x hx.le]
    change |1 - Real.sqrt (1 - x ^ 2)| < 1 / 2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · intro x hx y hy
    have hs := Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by linarith [hx2 x (by linarith)])
    have hp := Real.sqrt_nonneg (1 - x ^ 2)
    have hy' : 0 ≤ 1 - y := by linarith [(abs_lt.mp hy).2]
    rw [hFf x hx.le]
    change 0 < 2 * y - y ^ 2 - x ^ 2 ↔ 1 - Real.sqrt (1 - x ^ 2) < y
    have hsq := sq_lt_sq₀ hy' hp
    rw [← sub_lt_comm, ← hsq, hs]
    constructor <;> intro h <;> nlinarith

/-- The unit disk has actual globally smooth and Lipschitz local graph charts. -/
theorem isSmoothDomain_unitDisk : IsSmoothDomain (ball (0 : ℂ) 1) := by
  refine ⟨⟨isOpen_ball, isConnected_ball (by norm_num)⟩, fun p hp => ?_⟩
  rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hp
  have hp1 : ‖p‖ = 1 := by
    simp_all
  obtain ⟨K, F, hFc, hFl, hF0, hFb, hFiff⟩ := exists_unitDisk_graph
  let c : ℂ := -Complex.I * conj p
  have hc : ‖c‖ = 1 := by simp [c, hp1]
  have hcp : c * p = -Complex.I := by
    have hpp : conj p * p = (1 : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hp1]
      norm_num
    dsimp only [c]
    grind
  refine ⟨c, 1 / 8, 1 / 2, K, F, hc, by norm_num, by norm_num,
    hFc, hFl, hF0, hFb, ?_⟩
  intro w hwx hwy
  let q : ℂ := c * (w - p)
  change |q.re| < (1 / 8 : ℝ) at hwx
  change |q.im| < (1 / 2 : ℝ) at hwy
  change w ∈ ball (0 : ℂ) 1 ↔ F q.re < q.im
  have hcw : c * w = q - Complex.I := by
    dsimp only [q]
    rw [mul_sub, hcp]
    ring
  have hnorm : ‖w‖ ^ 2 = q.re ^ 2 + (q.im - 1) ^ 2 := by
    calc
      ‖w‖ ^ 2 = ‖c * w‖ ^ 2 := by simp [hc]
      _ = Complex.normSq (c * w) := (Complex.normSq_eq_norm_sq _).symm
      _ = q.re ^ 2 + (q.im - 1) ^ 2 := by
        rw [hcw, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
        ring
  rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg w), ← hFiff q.re hwx q.im hwy]
  constructor <;> intro h <;> nlinarith [hnorm]

/-- The disk therefore satisfies the domain hypothesis used by physical Green identities. -/
theorem isLipschitzDomain_unitDisk : IsLipschitzDomain (ball (0 : ℂ) 1) :=
  isSmoothDomain_unitDisk.isLipschitzDomain

theorem unitDisk_bounded : Bornology.IsBounded (ball (0 : ℂ) 1) :=
  Metric.isBounded_ball

theorem unitDisk_volume_toReal : (volume (ball (0 : ℂ) 1)).toReal = π := by simp

/-- The standard positively oriented circle is a genuine boundary parameter for the disk. -/
theorem unitCircle_isBoundaryParam :
    IsBoundaryParam (ball (0 : ℂ) 1) (circleMap 0 1) := by
  refine
    { lipschitz := ⟨Real.nnabs 1, lipschitzWith_circleMap 0 1⟩
      periodic := periodic_circleMap 0 1
      injOn := injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) (R := (1 : ℝ))
        (a := (0 : ℝ)) (b := 2 * π) (by norm_num) (by linarith)
      image := ?_
      const_speed := ?_
      area := ?_ }
  · rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply Subset.antisymm
    · rintro w ⟨θ, _, rfl⟩
      simp
    grind [image_circleMap_Ioc, abs_one]
  simp
  · have him : ∀ θ : ℝ,
        (conj (circleMap 0 1 θ) * deriv (circleMap 0 1) θ).im = 1 := by
      intro θ
      have hcc : conj (circleMap 0 1 θ) * circleMap 0 1 θ = (1 : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        simp
      rw [deriv_circleMap, ← mul_assoc, hcc]
      simp
    simp_rw [him]
    rw [intervalIntegral.integral_const, unitDisk_volume_toReal]
    simp

end PolyaNeumann

end
