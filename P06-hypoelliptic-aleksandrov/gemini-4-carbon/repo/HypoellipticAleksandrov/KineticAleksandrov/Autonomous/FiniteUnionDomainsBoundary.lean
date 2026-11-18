module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMeasures

/-! # The genuine physical terminal and lateral boundary of a finite disjoint union -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Component face points remain boundary points of the entire open union. -/
theorem FiniteIntervalUnion.frontier_component_subset (H : FiniteIntervalUnion)
    (i : Fin H.count) : frontier (H.component i).carrier ⊆ frontier H.carrier := by
  intro v hv
  rw [frontier, mem_sdiff, H.isOpen_carrier.interior_eq]
  refine ⟨closure_mono (H.component_subset i) (frontier_subset_closure hv), ?_⟩
  intro hmem
  obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
  by_cases hji : j = i
  · subst j
    exact Set.disjoint_left.mp
      (disjoint_frontier_iff_isOpen.mpr (show IsOpen (H.component i).carrier
        from isOpen_Ioo)) hv hj
  · have hd := (H.disjoint (Ne.symm hji)).closure_left (show IsOpen (H.component j).carrier
      from isOpen_Ioo)
    exact Set.disjoint_left.mp hd (frontier_subset_closure hv) hj

/-- The prescribed physical union exit has the true velocity frontier. -/
def finiteUnionExitSet (H : FiniteIntervalUnion) (sMinus T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ closure H.carrier} ∪
    {p | sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H.carrier}


/-- The genuine union exit is Borel. -/
theorem measurableSet_finiteUnionExitSet (H : FiniteIntervalUnion) (sMinus T : ℝ) :
    MeasurableSet (finiteUnionExitSet H sMinus T) := by
  unfold finiteUnionExitSet
  apply MeasurableSet.union
  · exact (isClosed_eq continuous_time continuous_const).measurableSet.inter
      (isClosed_closure.measurableSet.preimage
        (((continuous_apply 0).comp continuous_velocity).measurable))
  · convert ((isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isOpen_lt continuous_time continuous_const).measurableSet).inter
      (isClosed_frontier.measurableSet.preimage
        (((continuous_apply 0).comp continuous_velocity).measurable)) using 1
    ext p
    simp
    tauto

/-- The componentwise exit is supported on the actual union exit, with no lower-time defect. -/
theorem finiteUnionExit_compl_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    finiteUnionExit hH hLE hlam hLam A H T e (finiteUnionExitSet H sMinus T)ᶜ = 0  := by
  have reconstructionExit_subset_finiteUnionExitSet (i : Fin H.count) :
      reconstructionExit (H.component i) sMinus T ⊆ finiteUnionExitSet H sMinus T := by
    intro p hp
    rcases hp with hp | hp
    · refine Or.inl ⟨hp.1, closure_mono (H.component_subset i) ?_⟩
      change p.velocity 0 ∈ closure (Ioo (H.component i).lo (H.component i).hi)
      rw [closure_Ioo (H.component i).ordered.ne]
      exact hp.2
    · refine Or.inr ⟨hp.1, hp.2.1, H.frontier_component_subset i ?_⟩
      change p.velocity 0 ∈ frontier (Ioo (H.component i).lo (H.component i).hi)
      rw [frontier_Ioo (H.component i).ordered]
      simpa using hp.2.2
  apply le_antisymm _ (zero_le)
  apply (measure_mono (compl_subset_compl.mpr
    (reconstructionExit_subset_finiteUnionExitSet _))).trans
  exact le_of_eq ((strip_exit_probability hH hLE hlam hLam A (H.component (finiteUnionPoleIndex H T e)) sMinus T (finiteUnionComponentPole H T e) he).2.1)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
