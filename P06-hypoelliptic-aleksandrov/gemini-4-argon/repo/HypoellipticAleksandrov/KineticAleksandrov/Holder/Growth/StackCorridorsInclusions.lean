module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsPaths
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation

/-! # Strict cap margins and uniform comparison-box containment -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/- The initial tangent corridor lies in the source cap with strict spatial margins. -/
theorem initial_corridor_subset_cap {d } (P0 : KineticPoint d) {r }
    (hr : 0 < r) (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧
      v s = P0.velocity) :
    corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
      kineticAffine P0 r '' cap d := by
  intro Z hZ
  apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
  have hl := hleft _ hZ.1.2
  have hrel : relativePosition P0 Z = Z.position-x (Z.time-stackStartTime P0 r) := by
    rw [hl.1]
    ext i
    simp only [relativePosition, stackStartTime, stackStartPosition, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsq := pow_pos hr 2
  have hcube := pow_pos hr 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -(1/4 : ℝ) < (Z.time-P0.time)/r^2
    apply (lt_div_iff₀ hsq).mpr
    have := hZ.1.1
    dsimp [stackStartTime] at this
    nlinarith
  · change (Z.time-P0.time)/r^2 < -(1/8 : ℝ)
    apply (div_lt_iff₀ hsq).mpr
    have := hZ.1.2
    dsimp [stackStartTime] at this
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_position_norm P0 Z hr, hrel]
    apply (div_lt_iff₀ hcube).mpr
    have := hZ.2.1
    norm_num at *
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_velocity_norm P0 Z hr]
    apply (div_lt_iff₀ hr).mpr
    have hv := hZ.2.2
    rw [hl.2] at hv
    linarith

/- A uniformly bounded path corridor stays in the fixed comparison box. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
