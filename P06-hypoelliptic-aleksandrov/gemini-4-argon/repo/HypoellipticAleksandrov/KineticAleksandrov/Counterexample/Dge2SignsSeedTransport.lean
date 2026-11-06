module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import Mathlib.Tactic.FieldSimp

/-!
# Uniform transport positivity on the seed ball

The additive seed constant is chosen once by compactness on the position sphere
and the small velocity ball, before any point is quantified.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- The compact small seed ball over the Euclidean position sphere. -/
def smallSeedBall (d : ℕ) : Set (PDE.Vec d × PDE.Vec d) :=
  {q | PDE.vecNormSq q.2 = 1 ∧ PDE.vecEuclideanNorm (q.1 - q.2) ≤ 1 / 4}

/- The small seed ball is compact in the inherited native topology. -/
theorem isCompact_smallSeedBall (d : ℕ) : IsCompact (smallSeedBall d) := by
  have hclosed : IsClosed (smallSeedBall d) :=
    (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_snd) continuous_const).inter
      (isClosed_le (PDE.continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_snd))
        continuous_const)
  apply (isCompact_closedBall (0 : PDE.Vec d × PDE.Vec d) 2).of_isClosed_subset hclosed
  intro q hq
  obtain ⟨he, hy⟩ := hq
  have hen : PDE.vecEuclideanNorm q.2 = 1 := by simp [PDE.vecEuclideanNorm, he]
  have he' : ‖q.2‖ ≤ 1 := by simpa [hen] using PDE.norm_le_vecEuclideanNorm q.2
  have hy' : ‖q.1 - q.2‖ ≤ 1 / 4 := (PDE.norm_le_vecEuclideanNorm _).trans hy
  have htri : ‖q.1‖ ≤ ‖q.1 - q.2‖ + ‖q.2‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q.1 - q.2) q.2
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor <;> linarith

/- Increasing the additive seed constant has exactly the source's transport effect. -/
theorem ansatzTransport_seed_shift {d } (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    ansatzTransport alpha (seed alpha C₀ sigma) y e =
      ansatzTransport alpha (seed alpha 0 sigma) y e +
        PDE.vecDot y e * (alpha / 3 * C₀) := by
  rw [ansatzTransport_seed alpha C₀ sigma hsigma, ansatzTransport_seed alpha 0 sigma hsigma]
  unfold seed
  ring

/- The seed transport is continuous in both vector variables. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
