module

public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation

/-!
# Increasing events under the free box limit

Finite free FK boxes are monotone on every clopen increasing event of the
whole-lattice configuration space. The same comparison passes to the unique
free infinite-volume limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.Internal

noncomputable section

local instance rectangleInfiniteComparisonGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _

local instance rectangleInfiniteComparisonGenericEdgeDecidableEq
    {V : Type*} [Finite V] {G : SimpleGraph V} : DecidableEq G.edgeSet := Classical.decEq _

private theorem boxConfiguration_restriction_le {r s : ℕ} (hrs : r ≤ s)
    (hGH : (boxGraph (0, 0) r).map
        (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) ≤ boxGraph (0, 0) s)
    (B : Configuration (boxGraph (0, 0) s)) :
    boxConfiguration (0, 0) r
        (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH B) ≤
      boxConfiguration (0, 0) s B := by
  intro e he
  rw [boxConfiguration_open_iff] at he ⊢
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
  refine Finset.mem_map.mpr ⟨_, (mem_embeddedConfigurationRestriction _ _ _ _ B a).mp ha, ?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map _ a.val) = Sym2.map Subtype.val a.val
  rw [Sym2.map_map]; rfl

private theorem boxProbabilityMeasure_event_eq_expectation (q : Parameters)
    (r : ℕ) (E : Set LatticeConfiguration) (hE : MeasurableSet E) :
    (((boxProbabilityMeasure q (0, 0) r : ProbabilityMeasure LatticeConfiguration) E : NNReal) : ℝ) =
      FiniteProbability.expectation (law (boxGraph (0, 0) r) q (BoundaryCondition.free ∅))
        (Set.indicator ({A | boxConfiguration (0, 0) r A ∈ E} :
          Set (Configuration (boxGraph (0, 0) r))) (fun _ => (1 : ℝ))) := by
  have hpre :
      ((boxProbabilityMeasure q (0, 0) r : Measure LatticeConfiguration) E) =
        measure (boxGraph (0, 0) r) q (BoundaryCondition.free ∅)
          {A | boxConfiguration (0, 0) r A ∈ E} :=
    PMF.toMeasure_map_apply _ _ _ measurable_from_top hE
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def, hpre,
    measure_toReal_eq_indicator_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : boxConfiguration (0, 0) r A ∈ E <;>
    simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos _ q _ A).le]

/-- The free origin-box laws are increasing on every clopen increasing event
of the actual whole-lattice configuration space. -/
theorem boxProbabilityMeasure_clopen_upper_mono (q : Parameters)
    (r s : ℕ) (hrs : r ≤ s) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤ boxProbabilityMeasure q (0, 0) s E := by
  classical
  let f := boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  have hGH : (boxGraph (0, 0) r).map f ≤ boxGraph (0, 0) s :=
    boxGraph_map_boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  let S : Set (Configuration (boxGraph (0, 0) r)) := {A | boxConfiguration (0, 0) r A ∈ E}
  let F : Configuration (boxGraph (0, 0) r) → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hF0 (A) : 0 ≤ F A := by by_cases hA : A ∈ S <;> simp [F, hA]
  have hF : Monotone F := fun A B hAB => by
    by_cases hA : A ∈ S
    · simp [F, hA, show B ∈ S from hEupper (boxConfiguration_mono (0, 0) r hAB) hA]
    · simp [F, hA, hF0 B]
  refine NNReal.coe_le_coe.mp ?_
  rw [boxProbabilityMeasure_event_eq_expectation q r E hEclopen.2.measurableSet,
    boxProbabilityMeasure_event_eq_expectation q s E hEclopen.2.measurableSet]
  refine (embedded_free_expectation_le (boxGraph (0, 0) r) (boxGraph (0, 0) s)
    f hGH q ∅ ∅ F hF0 hF).trans <| FiniteProbability.expectation_mono _ _ _ fun B => ?_
  by_cases hsmall : boxConfiguration (0, 0) r
      (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s) f hGH B) ∈ E
  · simp [F, S, Set.indicator, hsmall, hEupper (boxConfiguration_restriction_le hrs hGH B) hsmall]
  · by_cases hlarge : boxConfiguration (0, 0) s B ∈ E <;>
      simp [F, S, Set.indicator, hsmall, hlarge]

/-- Every finite free origin-box probability of a clopen increasing event is
bounded by its probability under the unique free infinite-volume limit. -/
theorem freeBoxLimit_clopen_upper_ge_box (q : Parameters)
    (r : ℕ) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)) E := by
  have hweak := ((Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
    (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive).comp
    (tendsto_atTop.2 fun b => by filter_upwards [eventually_ge_atTop b] with n _; omega
      : Tendsto (fun n : ℕ => n + r) atTop atTop)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hEclopen) fun n =>
      boxProbabilityMeasure_clopen_upper_mono q r (n + r) (by omega) E hEclopen hEupper

end
end PottsDiscontinuity.TorusLoops
