module

public import PottsDiscontinuity.TorusLoops.LoopDensityLogBounds
public import PottsDiscontinuity.TorusLoops.LoopTailBoundaryDecay

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

/-- The height-normalized logarithm of the loop correction is eventually
small at every sufficiently large width. -/
theorem loopDensityLogRate_eventually_small
    (q : Set.Ici (1 : ℝ))
    (hzero : Tendsto (fun n => (((Classical.choose (freeBoxLimit_existsUnique
      (rectangleFKParameters q))) (boundaryConnectionEvent n) : NNReal) : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (hN : Even N) (hNp : 0 < N),
      ∀ᶠ m : ℕ in atTop, |windingLoopDensityLogRate hN hNp q m| ≤ ε := by
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  have hC₁ := windingLoopDensityLogSlope_nonneg q
  obtain ⟨r, hr⟩ := exists_nat_gt (C₁ / ε)
  have hr0 : 0 < r := by
    have hrR := (div_nonneg hC₁ hε.le).trans_lt hr
    exact_mod_cast hrR
  have hfirst : C₁ / (2 * (r : ℝ)) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [(div_lt_iff₀ hε).1 hr]
  have harm := (tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero).eventually
    (Iio_mem_nhds (windingLoopTailArmThreshold_pos q r))
  filter_upwards [harm] with N hNarm hN hNp
  have ht : Tendsto (fun m : ℕ => (2 * (m + 1) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun m => by linarith [Nat.cast_nonneg (α := ℝ) m]) tendsto_natCast_atTop_atTop
  have hrem := (ht.const_div_atTop (C₀ + C₁)).eventually (Iio_mem_nhds (show 0 < ε / 2 by positivity))
  filter_upwards [hrem, eventually_ge_atTop N, eventually_ge_atTop (9 * N * r)] with m hm hmN hmr
  have hdiv : 9 * N ≤ (m + 1) / r := (Nat.le_div_iff_mul_le hr0).2 (by omega)
  have h := abs_windingLoopDensityLogRate_le hN hNp q r m hr0 (by omega) (by omega) hNarm.le
  push_cast at h
  linarith

end PottsDiscontinuity.TorusLoops
