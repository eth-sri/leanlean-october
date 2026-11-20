module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Passing the finite collar estimate to the actual limit

The collar distance is measured from the original moving boundary. Its modulus
has no approximation-index or transported-radius dependence.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- The actual limit inherits the original-boundary collar estimate from the
actual finite approximants. -/
theorem abs_le_collar_innerBall_dirichlet_limit
    {n : ℕ} (E : InnerBallExhaustion n)
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    ∀ p ∈ E.innerClosed δ0 S0,
      |E.pointLimit p| ≤ E.C *
        (barrierW (collarKappa E.L E.lam) (E.r0 - PDE.vecEuclideanNorm (p.position - E.Γ p.time)) /
          barrierW (collarKappa E.L E.lam) E.d) := by
  have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S0) E hδ0 hδr
  have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr E.β E.R E.tendsto_gap E.tendsto_radius E.g E.close
  intro p hp
  apply le_of_tendsto (hU.tendsto_at hp |>.abs)
  filter_upwards [hmem, E.tendsto_gap.eventually (gt_mem_nhds E.hd)] with k hk hβk
  exact abs_le_original_collar_straightened_dirichlet
    E.hlam E.hB E.hBs E.hbs E.haα E.hατ hk.2.1 (E.gap_pos k).le hβk.le E.hd E.hdr (E.smooth k) E.hL
    (E.lipschitz k) (E.close k) E.hε E.hC E.F E.hFC E.hsupp (E.u k) (E.solution k) p
    ⟨⟨hp.1.1, hp.1.2.1⟩, subset_closure (hk.2.2 p hp)⟩

end HypoellipticAleksandrov.KineticAleksandrov
