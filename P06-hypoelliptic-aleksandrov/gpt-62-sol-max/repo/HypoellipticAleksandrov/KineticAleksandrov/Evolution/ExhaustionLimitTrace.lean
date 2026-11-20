module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Exact uniform bound and terminal/lateral traces of the exhaustion candidate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- The continuous zero extension has the original uniform bound and terminal
values, and vanishes on the actual moving lateral boundary. -/
theorem innerBallDirichletLimit_bound_terminal_lateral
    {n : ℕ} (E : InnerBallExhaustion n) :
    (∀ p ∈ E.closedSlab,
      |E.limit p| ≤ E.C) ∧
    (∀ p ∈ E.closedSlab, p.time = E.τ →
      E.limit p = E.F (p.position, p.velocity)) ∧
    (∀ p : KineticPoint n,
      p.position ∈ frontier (movingDomain E.domain E.Γ p.time) →
      E.limit p = 0) := by
  have hr0 := E.radius_pos
  have hpoint (p : KineticPoint n)
      (hp : p ∈ E.closedSlab)
      (hi : p.position ∈ movingDomain E.domain E.Γ p.time) :
      |E.limit p| ≤ E.C := by
    obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin E.hΓ hr0 hp hi
    rw [E.limit_eq hi]
    exact (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S) E hδ hδr).2 p hpK
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    by_cases hi : p.position ∈ movingDomain E.domain E.Γ p.time
    · exact hpoint p hp hi
    · simpa only [InnerBallExhaustion.limit, ite_eq_right hi, abs_zero] using E.hC
  · intro p hp ht
    by_cases hi : p.position ∈ movingDomain E.domain E.Γ p.time
    · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
        exists_innerClosedCylinder_mem_nhdsWithin E.hΓ hr0 hp hi
      have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S) E hδ hδr
      have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S)
        hδ hδr E.β E.R E.tendsto_gap E.tendsto_radius E.g E.close
      have he : ∀ᶠ k : ℕ in atTop,
          straightenedPullback (E.g k) (E.u k) p = E.F (p.position, p.velocity) := by
        filter_upwards [hmem] with k hk
        have hm := subset_closure (hk.2.2 p hpK)
        simp only [straightenedPoint, ht] at hm
        have het := (E.solution k).2.2.2.1 _ hm
        simpa only [straightenedPullback, straightenedPoint, ht,
          spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using het
      rw [E.limit_eq hi]
      exact tendsto_nhds_unique (hU.tendsto_at hpK)
        (tendsto_const_nhds.congr' (he.mono fun k hk => hk.symm))
    · have hzero : E.F (p.position, p.velocity) = 0 := by
        by_contra hne
        have hs := E.hsupp (p.position, p.velocity)
          (subset_tsupport (E.F : EvolutionAmbientState n → ℝ) hne)
        have hn := (mem_movingBall_iff_norm_lt hr0).not.mp hi
        rw [ht] at hn
        linarith [E.hd]
      simp only [InnerBallExhaustion.limit, ite_eq_right hi, hzero]
  · intro p hp
    have hnot : p.position ∉ movingDomain E.domain E.Γ p.time :=
      by
        have hopen := isOpen_movingDomain (γ := E.Γ) (PDE.isOpen_euclideanBall 0 E.r0) p.time
        change p.position ∈ closure _ ∧ p.position ∉ interior _ at hp
        simpa only [hopen.interior_eq] using hp.2
    exact ite_eq_right hnot

end HypoellipticAleksandrov.KineticAleksandrov
