module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCollar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuous lateral-zero extension of the actual ball exhaustion limit

The limit is extended by zero outside the original diffused interior. Inner
cylinder continuity controls interior points and the proved collar controls the boundary.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

section
variable {n : ℕ} (E : InnerBallExhaustion n)

/-- The zero extension inherits the collar estimate on the entire original closed slab. -/
theorem abs_le_collar_innerBallDirichletLimit :
    ∀ p ∈ E.closedSlab,
      |E.limit p| ≤ E.C *
        (barrierW (collarKappa E.L E.lam) (E.r0 - PDE.vecEuclideanNorm (p.position - E.Γ p.time)) /
          barrierW (collarKappa E.L E.lam) E.d) := by
  have hr0 := E.radius_pos
  intro p hp
  by_cases hi : p.position ∈ movingDomain E.domain E.Γ p.time
  · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin E.hΓ hr0 hp hi
    rw [E.limit_eq hi]
    exact abs_le_collar_innerBall_dirichlet_limit (S0 := S) E hδ hδr p hpK
  · have hn :=
      le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
        (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
    simp only [InnerBallExhaustion.limit, ite_eq_right hi, hn, sub_self, barrierW,
      mul_zero, Real.exp_zero, zero_div, mul_zero, abs_zero, le_refl]

/-- The actual exhaustion limit, extended by zero on the diffused boundary, is continuous
on the entire original closed slab, including its time faces. -/
theorem continuousOn_innerBallDirichletLimit :
    ContinuousOn (E.limit)
      (E.closedSlab) := by
  have hr0 := E.radius_pos
  let K := E.closedSlab
  have hbound := abs_le_collar_innerBallDirichletLimit E
  intro p hp
  by_cases hi : p.position ∈ movingDomain E.domain E.Γ p.time
  · obtain ⟨δ, S, hδ, hδr, hpK, hKnhds⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin E.hΓ hr0 hp hi
    have hc := (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S) E hδ hδr).1 p hpK
    have heq : ∀ q ∈ E.innerClosed δ S, E.limit q =
        E.pointLimit q :=
      fun q hq => E.limit_eq
        (innerClosedCylinder_subset_movingBall hδ hδr hq)
    exact (hc.congr heq (E.limit_eq hi)).mono_of_mem_nhdsWithin
      hKnhds
  · have hn : PDE.vecEuclideanNorm (p.position - E.Γ p.time) = E.r0 :=
      le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
        (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
    let G (q : KineticPoint n) := E.C *
      (barrierW (collarKappa E.L E.lam) (E.r0 - PDE.vecEuclideanNorm (q.position - E.Γ q.time)) /
        barrierW (collarKappa E.L E.lam) E.d)
    have hdist : Continuous (fun q : KineticPoint n =>
        PDE.vecEuclideanNorm (q.position - E.Γ q.time)) :=
      PDE.continuous_vecEuclideanNorm.comp
        (continuous_position.sub (E.hΓ.comp continuous_time))
    have hGc : Continuous G := by dsimp [G, barrierW]; fun_prop
    have hGp : G p = 0 := by
      simp only [G, hn, sub_self, barrierW, mul_zero, Real.exp_zero, zero_div, mul_zero]
    have hGlim : Tendsto G (𝓝[K] p) (𝓝 0) :=
      hGp ▸ hGc.continuousWithinAt.tendsto
    have hKmem : ∀ᶠ q in 𝓝[K] p, q ∈ K := self_mem_nhdsWithin
    have hz : Tendsto (E.limit) (𝓝[K] p) (𝓝 0) :=
      squeeze_zero_norm' (hKmem.mono fun q hq =>
        (show ‖E.limit q‖ ≤ G q from
          (by rw [Real.norm_eq_abs]; exact hbound q hq))) hGlim
    simpa only [ContinuousWithinAt, InnerBallExhaustion.limit, ite_eq_right hi] using hz

end

end HypoellipticAleksandrov.KineticAleksandrov
