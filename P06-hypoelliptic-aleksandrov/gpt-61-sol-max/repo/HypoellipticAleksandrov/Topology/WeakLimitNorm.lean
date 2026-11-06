module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Order.OrderClosed

/-!
# Weak-limit norm bounds

This module records the dual-functional proof that a uniformly norm-bounded
sequence has a norm-bounded weak limit.
-/

 public section

open Filter
open scoped Topology

namespace HypoellipticAleksandrov

/-- A uniform norm bound is inherited by a limit that converges under every
continuous real linear functional. -/
theorem norm_le_of_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℕ → H) (v : H) (R : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hweak : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v))) :
    ‖v‖ ≤ R := (NormedSpace.norm_le_dual_bound ℝ v (LE.le.trans (norm_nonneg (u 0)) (hu 0)) fun ell =>
  le_of_tendsto' (Tendsto.norm (hweak ell)) fun n =>
    Trans.trans
      (Trans.trans (ContinuousLinearMap.le_opNorm ell (u n)) (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg ell)))
      (mul_comm ‖ell‖ R))

end HypoellipticAleksandrov
