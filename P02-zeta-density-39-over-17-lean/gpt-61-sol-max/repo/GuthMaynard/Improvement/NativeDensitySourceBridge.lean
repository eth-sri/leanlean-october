module
import Mathlib
public import GuthMaynard.Improvement.NativeDensityConventionBridge
public import GuthMaynard.NativeSource.GuthMaynard.ZeroCount
public import GuthMaynard.NativeSource.GuthMaynard.Asymptotics

@[expose] public section

open Complex Filter MathCollab.Density

namespace GuthMaynard.Improvement

/-- Literal shared native count equals the audited actual count, including
 analytic multiplicity and both closed height endpoints. -/
theorem native_N_eq_zetaDensityCount {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    NativeMoment.N σ T = zetaDensityCount σ T := by
  unfold NativeMoment.N NativeMoment.zeroCountRect NativeMoment.analyticVanishingOrder
  apply native_rectangle_sum_eq_zetaDensityCount hσ
  intro ρ
  simp only [NativeMoment.zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    NativeMoment.ZeroRectangle, Set.mem_ofPred_eq]
  tauto

/-- Exact native epsilon-asymptotic estimate transfers to the actual all-height
 count. The analytic estimate remains a displayed parameter. -/
theorem native_density_epsilon_bound {σ p : ℝ} (hσ : 0 < σ) (hp : 0 ≤ p)
    (hb : NativeMoment.EpsilonPowerBound (fun T => (NativeMoment.N σ T:ℝ))
      (fun T => T^p)) {ε : ℝ} (hε : 0 < ε) :
    MathCollab.Density.ZetaBound σ ((p+ε)) := by
  have hh := hb ε hε
  simp only [native_N_eq_zetaDensityCount hσ] at hh
  exact zetaDensityCount_bound_of_native_bigO hp hε hh


