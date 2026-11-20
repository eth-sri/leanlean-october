module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Locally uniform limits of actual Dirichlet approximants

Completeness is applied to the proved uniform Cauchy property. The pointwise
limit is the same function on all inner cylinders, irrespective of their sizes.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

abbrev InnerBallExhaustion.innerOpen {n : ℕ} (E : InnerBallExhaustion n) (δ S : ℝ) :=
  boundedInnerOpenCylinder (E.r0 - δ) E.Γ E.α E.τ S

section
variable {n : ℕ} (E : InnerBallExhaustion n)

/-- The actual finite Dirichlet sequence converges uniformly on every bounded inner
cylinder to its pointwise limit. -/
theorem tendstoUniformlyOn_innerBall_dirichlet
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    TendstoUniformlyOn (E.approximant)
      (fun p => E.pointLimit p) atTop
      (E.innerClosed δ0 S0) := by
  have h := uniformCauchySeqOn_innerBall_dirichlet (S0 := S0) E hδ0 hδr
  exact h.tendstoUniformlyOn_of_tendsto (fun p hp => (h.cauchySeq hp).tendsto_limUnder)

/-- The approximants are eventually continuous and uniformly bounded on the fixed compact cylinder. -/
theorem eventually_continuousOn_abs_le_innerBall
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    ∀ᶠ k : ℕ in atTop,
      ContinuousOn (straightenedPullback (E.g k) (E.u k))
        (E.innerClosed δ0 S0) ∧
      ∀ p ∈ E.innerClosed δ0 S0,
        |straightenedPullback (E.g k) (E.u k) p| ≤ E.C := by
  let K := E.innerClosed δ0 S0
  have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr E.β E.R E.tendsto_gap E.tendsto_radius E.g E.close
  have hclosed (k : ℕ) (hk : 0 < E.r0 - E.β k ∧ 0 < E.R k ∧
      ∀ p ∈ K, (straightenedPoint (E.g k) p).2 ∈
        openEllipsoid (straightenedEllipsoidMatrix n (E.r0 - E.β k) (E.R k))) :
      MapsTo (straightenedPoint (E.g k)) K
        (scalarParabolicClosedCylinder E.a E.τ
          (openEllipsoid (straightenedEllipsoidMatrix n (E.r0 - E.β k) (E.R k)))) :=
    fun p hp => ⟨⟨E.haα.le.trans hp.1.1, hp.1.2.1⟩, subset_closure (hk.2.2 p hp)⟩
  exact hmem.mono fun k hk => ⟨(E.solution k).1.comp
    (continuous_straightenedPoint (E.smooth k).continuous).continuousOn (hclosed k hk),
    fun p hp => abs_le_straightened_dirichlet E.hlam E.hB E.hBs E.hbs (E.haα.trans E.hατ) hk.1 hk.2.1
      (E.smooth k) E.hε E.F (E.u k) (E.solution k) E.hC E.hFC _ (hclosed k hk hp)⟩

/-- The actual exhaustion limit is continuous and has the original uniform bound on
every bounded inner cylinder. -/
theorem continuousOn_bounded_innerBall_dirichlet_limit
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    ContinuousOn (fun p => E.pointLimit p)
      (E.innerClosed δ0 S0) ∧
    ∀ p ∈ E.innerClosed δ0 S0,
      |E.pointLimit p| ≤ E.C := by
  have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S0) E hδ0 hδr
  have hbd := eventually_continuousOn_abs_le_innerBall (S0 := S0) E hδ0 hδr
  exact ⟨hU.continuousOn (hbd.mono (fun _ h => h.1)).frequently, fun p hp =>
    le_of_tendsto (hU.tendsto_at hp |>.abs) (hbd.mono fun _ h => h.2 p hp)⟩

end

end HypoellipticAleksandrov.KineticAleksandrov
