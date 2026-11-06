module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionRegularity

/-! # Compact windows and scalar jet bounds for position convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Position convolution of the continuous extension, in physical coordinate order. -/
def positionBarrierConvolution (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∫ Y, barrierConvolutionIntegrand κ phi q Y

variable (κ : ℝ → ℝ)

/-- Compact scalar kernels and both derivatives have simultaneous finite global bounds. -/
theorem barrier_kernel_uniform_bounds  (hκ : ContDiff ℝ 2 κ)
    (hs : HasCompactSupport κ) :
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧
      (∀ x, |κ x| ≤ K0) ∧ (∀ x, |deriv κ x| ≤ K1) ∧
        ∀ x, |deriv (deriv κ) x| ≤ K2 := by
  obtain ⟨hc1, hc2⟩ := barrier_kernel_derivatives_continuous κ hκ
  obtain ⟨K0, hb0⟩ := hκ.continuous.bounded_above_of_compact_support hs
  obtain ⟨K1, hb1⟩ := hc1.bounded_above_of_compact_support hs.deriv
  obtain ⟨K2, hb2⟩ := hc2.bounded_above_of_compact_support hs.deriv.deriv
  refine ⟨max K0 0, max K1 0, max K2 0, le_max_right _ _, le_max_right _ _,
    le_max_right _ _, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  simp_all

/-- Both scalar coordinates of a parameter in the unit ball stay in their unit intervals. -/
theorem barrier_parameter_ball_bounds {q q0 : ℝ × ℝ} (hq : q ∈ Metric.ball q0 1) :
    |q.1 - q0.1| < 1 ∧ |q.2 - q0.2| < 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hq
  aesop

/-- A compact integration window contains every nearby translated kernel support. -/
theorem barrier_convolution_support_window  (hs : HasCompactSupport κ)
    (q0 : ℝ × ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ q ∈ Metric.ball q0 1, ∀ Y : ℝ, Y ∉ Icc (-R) R →
      κ (q.1 - Y) = 0 ∧ deriv κ (q.1 - Y) = 0 ∧ deriv (deriv κ) (q.1 - Y) = 0 := by
  obtain ⟨S, hS, hSb⟩ := hs.isBounded.exists_pos_norm_lt
  let R := |q0.1| + S + 2
  refine ⟨R, by positivity, fun q hq Y hY => ?_⟩
  have hqX := (barrier_parameter_ball_bounds hq).1
  have hn : q.1 - Y ∉ tsupport κ := by
    intro ht
    have hsmall := hSb _ ht
    rw [Real.norm_eq_abs] at hsmall
    grind
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun hh => hn (tsupport_deriv_subset hh))⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
