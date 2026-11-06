module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Tactic

/-! # Tangent-extended Hermite paths with uniform stack bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/- Increasing the acceleration bound preserves a skeleton. -/
theorem skeleton_mono_bound {d } {x v : ℝ → PDE.Vec d} {H K a b }
    (hx : IsSkeleton x v H a b) (hHK : H ≤ K) : IsSkeleton x v K a b :=
  ⟨hx.1, hx.2.1, fun s hs t ht => (hx.2.2 s hs t ht).trans
    (mul_le_mul_of_nonneg_right hHK (abs_nonneg _))⟩

/- The cap-center free-transport displacement equals the path displacement. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
