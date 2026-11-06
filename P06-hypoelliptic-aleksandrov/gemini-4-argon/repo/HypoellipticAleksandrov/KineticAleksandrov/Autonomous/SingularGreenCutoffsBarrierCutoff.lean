module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling

/-! # Actual rectangular cutoffs for sublinear Bellman barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/- A fixed unit inner radius and two-unit outer radius cutoff. -/
def barrierCutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/- The same scalar cutoff is used on the two different kinetic scales. -/
def barrierCutoff : ℝ → ℝ := barrierCutoffBump

/- The cutoff takes values in the source unit interval. -/
theorem barrierCutoff_bounds (x : ℝ) : 0 ≤ barrierCutoff x ∧ barrierCutoff x ≤ 1 :=
  ⟨barrierCutoffBump.nonneg, barrierCutoffBump.le_one⟩

/- The fixed cutoff is C∞. -/
theorem barrierCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) barrierCutoff :=
  barrierCutoffBump.contDiff

/- The cutoff and both actual derivatives vanish outside its outer interval. -/
theorem barrierCutoff_zero_jets {x } (hx : 2 < |x|) :
    barrierCutoff x = 0 ∧ deriv barrierCutoff x = 0 ∧
      deriv (deriv barrierCutoff) x = 0 := by
  have hn : x ∉ tsupport barrierCutoff := by
    rw [barrierCutoff, barrierCutoffBump.tsupport_eq]
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le, barrierCutoffBump] using hx
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

/- The two scalar derivative bounds are fixed before any coefficient or spatial scale. -/
theorem barrierCutoff_derivative_bounds : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    (∀ x, |deriv barrierCutoff x| ≤ D1) ∧
    (∀ x, |deriv (deriv barrierCutoff) x| ≤ D2) := by
  obtain ⟨_, D1, D2, _, hD1, hD2, _, h1, h2⟩ := barrier_kernel_uniform_bounds
    barrierCutoff (barrierCutoff_contDiff.of_le (by simp)) barrierCutoffBump.hasCompactSupport
  exact ⟨D1, D2, hD1, hD2, h1, h2⟩

/- The physical rectangular cutoff, centered at the barrier's position singularity. -/
def barrierRectCutoff (Y R : ℝ) (z : ℝ × ℝ) : ℝ :=
  barrierCutoff ((z.1 - Y) / R ^ 3) * barrierCutoff (z.2 / R)

/- The rectangular cutoff remains between zero and one. -/
theorem barrierRectCutoff_bounds (Y R : ℝ) (z : ℝ × ℝ) :
    0 ≤ barrierRectCutoff Y R z ∧ barrierRectCutoff Y R z ≤ 1 := by
  exact ⟨mul_nonneg (barrierCutoff_bounds _).1 (barrierCutoff_bounds _).1,
    (mul_le_mul (barrierCutoff_bounds _).2 (barrierCutoff_bounds _).2
      (barrierCutoff_bounds _).1 zero_le_one).trans_eq (one_mul _)⟩

/- The literal rectangular cutoff is continuous on the physical plane. -/
theorem barrierRectCutoff_continuous (Y R : ℝ) : Continuous (barrierRectCutoff Y R) :=
  (barrierCutoff_contDiff.continuous.comp
    ((continuous_fst.sub continuous_const).div_const _)).mul
      (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))

/- Multiplication by the literal kinetic rectangle produces a compact physical test. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
