module

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace PottsDiscontinuity.RCInfinite
open FK FK.FiniteProbability
open scoped Classical
noncomputable section

section General
variable {α β : Type*}

/-- Exact disintegration of a PMF over the fibers of an observation. -/
theorem pmf_eq_bind_fiber_filter (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) :
    p = (p.map f).bind (fun b => p.filter {x | f x = b} (hf b)) := by
  classical
  have hden (b : β) : (∑' x, ({x | f x = b} : Set α).indicator p x) = (p.map f) b := by
    rw [PMF.map_apply]; exact tsum_congr fun x => by simp [Set.indicator, eq_comm]
  ext a
  symm
  rw [PMF.bind_apply]
  have hterm (b : β) : (p.map f) b * (p.filter {x | f x = b} (hf b)) a =
      if b = f a then p a else 0 := by
    rw [PMF.filter_apply, hden]
    by_cases hb : b = f a
    · subst b
      obtain ⟨x, hx, hxp⟩ := hf (f a)
      have hpos : (p.map f) (f a) ≠ 0 := (PMF.mem_support_map_iff f p (f a)).2 ⟨x, hxp, hx⟩
      simp only [Set.indicator_of_mem (s := {x | f x = f a}) rfl, ite_true]
      rw [mul_left_comm, ENNReal.mul_inv_cancel hpos ((p.map f).apply_ne_top (f a)), mul_one]
    · simp [Set.indicator_of_notMem (s := {x | f x = b}) (fun h => hb h.symm), hb]
  simp_rw [hterm]
  simp

variable [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_measureReal_eq_expectation (p : PMF α) (A : Set α) :
    (p.toMeasure A).toReal = expectation p (A.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [PMF.toMeasure_apply_fintype,
    ENNReal.toReal_sum fun a _ => by by_cases ha : a ∈ A <;> simp [Set.indicator, ha, p.apply_ne_top]]
  exact Finset.sum_congr rfl fun a _ => by by_cases ha : a ∈ A <;> simp [Set.indicator, ha]

/-- A joint event is the average of its conditional probabilities, restricted
to the selected observed states. -/
theorem pmf_joint_fiber_sum (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α) (T : Set β) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *
        (if b ∈ T then ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal else 0) := by
  classical
  rw [pmf_measureReal_eq_expectation]
  conv_lhs => rw [pmf_eq_bind_fiber_filter p f hf, expectation_bind]
  unfold expectation
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  change expectation (p.filter {x | f x = b} (hf b))
      ((S ∩ f ⁻¹' T).indicator (fun _ => (1 : ℝ))) = _
  rw [← pmf_measureReal_eq_expectation]
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true]
    refine congrArg ENNReal.toReal (PMF.toMeasure_apply_eq_of_inter_support_eq _
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet ?_)
    ext a
    exact ⟨fun ⟨⟨ha, _⟩, hp⟩ => ⟨ha, hp⟩, fun ⟨ha, hp⟩ =>
      ⟨⟨ha, (show f a ∈ T from ((PMF.mem_support_filter_iff _).mp hp).1.symm ▸ hbT)⟩, hp⟩⟩
  · simp only [hbT, ite_false, ENNReal.toReal_eq_zero_iff]
    exact Or.inl <| (PMF.toMeasure_apply_eq_zero_iff _ (Set.toFinite _).measurableSet).2 <|
      Set.disjoint_left.mpr fun a hp ha => hbT (((PMF.mem_support_filter_iff _).mp hp).1 ▸ ha.2)

theorem pmf_joint_le_of_fiber_le (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (c : ℝ)
    (h : ∀ b, ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal ≤ c) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal ≤ c * (p.toMeasure (f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum p f hf S T, show (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0) by
    rw [pmf_measureReal_eq_expectation]
    simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator fun _ => (1 : ℝ))).symm,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (h b) (ENNReal.toReal_nonneg (a := (p.map f) b))]
  · simp [hbT]

theorem pmf_joint_ge_of_fiber_ge (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (c : ℝ)
    (h : ∀ b, c ≤ ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal) :
    c * (p.toMeasure (f ⁻¹' T)).toReal ≤ (p.toMeasure (S ∩ f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum p f hf S T, show (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0) by
    rw [pmf_measureReal_eq_expectation]
    simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator fun _ => (1 : ℝ))).symm,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (h b) (ENNReal.toReal_nonneg (a := (p.map f) b))]
  · simp [hbT]

end General

section Embedded
variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)

attribute [local instance] configurationMeasurableSpace
local instance outerEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance innerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance outerEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance removedFintype (R : Configuration H) : Fintype (RemovedConfiguration H R) :=
  Fintype.ofFinite _

theorem embedded_filter_probability (θ : Parameters) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (S : Set (Configuration G)) :
    (((law H θ ξ).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K)).toMeasure
        ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S)) =
      measure G θ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S := by
  have h := congrArg (fun p : PMF (Configuration G) => p.toMeasure S)
    (law_filter_frozen_map_embeddedRestriction G H f hGH θ ξ K)
  rwa [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at h

omit [Finite W] in
theorem split_second_fiber (R : Configuration H) (K : RemovedConfiguration H R) :
    {C | (configurationSplitEquiv H R C).2 = K} = frozenStateEvent R K := by
  ext C; exact Subtype.ext_iff

/-- The conditional upper comparison remains valid after intersecting with an
arbitrary event of the exterior edge state. -/
theorem embedded_joint_le (θ : Parameters) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V) (S : Set (Configuration G)) (hS : IsUpperSet S)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))) :
    (measure H θ ξ
      (((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) ∩
        (fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal ≤
      (measure G θ η S).toReal *
        (measure H θ ξ
          ((fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  refine pmf_joint_le_of_fiber_le (law H θ ξ) (fun C => (configurationSplitEquiv H R C).2)
    (fun K => by simpa only [split_second_fiber] using frozenStateEvent_support θ ξ R K)
    ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) T (measure G θ η S).toReal fun K => ?_
  simp only [split_second_fiber H R K]
  rw [embedded_filter_probability G H f hGH θ ξ K S]
  exact measure_boundary_comparison θ _ η (hpart K) S hS

/-- The conditional lower comparison with the free law also remains valid
after intersecting with an arbitrary exterior-state event. -/
theorem embedded_joint_ge (θ : Parameters) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V) (S : Set (Configuration G)) (hS : IsUpperSet S)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      η.partition ≤ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))) :
    (measure G θ η S).toReal *
        (measure H θ ξ
          ((fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal ≤
      (measure H θ ξ
        (((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) ∩
          (fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  refine pmf_joint_ge_of_fiber_ge (law H θ ξ) (fun C => (configurationSplitEquiv H R C).2)
    (fun K => by simpa only [split_second_fiber] using frozenStateEvent_support θ ξ R K)
    ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) T (measure G θ η S).toReal fun K => ?_
  simp only [split_second_fiber H R K]
  rw [embedded_filter_probability G H f hGH θ ξ K S]
  exact measure_boundary_comparison θ η _ (hpart K) S hS

end Embedded
end
end PottsDiscontinuity.RCInfinite
