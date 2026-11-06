module

public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation

/-!
# Increasing events under the free box limit

Finite free FK boxes are monotone on every clopen increasing event of the
whole-lattice configuration space. The same comparison passes to the unique
free infinite-volume limit.
-/

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.Internal

noncomputable section

local instance rectangleInfiniteComparisonGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _


section
variable {r s : ℕ} (hrs : r ≤ s) (hGH : (boxGraph (0, 0) r).map (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) ≤ boxGraph (0, 0) s)
theorem originBoxEdgeEmbedding_compatible (e : (boxGraph (0, 0) r).edgeSet) :
    boxEdgeEmbedding (0, 0) s
        (embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH e) =
      boxEdgeEmbedding (0, 0) r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex (0, 0) s => v.val)
      (Sym2.map (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) e.val) =
    Sym2.map (fun v : BoxVertex (0, 0) r => v.val) e.val
  rw [Sym2.map_map]
  rfl

theorem boxConfiguration_restriction_le (B : Configuration (boxGraph (0, 0) s)) :
    boxConfiguration (0, 0) r
        (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH B) ≤
      boxConfiguration (0, 0) s B := by
  intro e he
  rw [boxConfiguration_open_iff] at he ⊢
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp he
  apply Finset.mem_map.mpr
  refine ⟨embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
    (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH a, ((mem_embeddedConfigurationRestriction _ _ _ _ B a).mp ha), ?_⟩
  calc
    boxEdgeEmbedding (0, 0) s
        (embeddedEdgeEmbedding (boxGraph (0, 0) r) (boxGraph (0, 0) s)
          (boxVertexEmbedding (latticeBox_mono (0, 0) hrs)) hGH a) =
      boxEdgeEmbedding (0, 0) r a := originBoxEdgeEmbedding_compatible hrs hGH a
    _ = e := hae
end

section
variable (q : Parameters)
theorem boxProbabilityMeasure_event_eq_expectation (r : ℕ) (E : Set LatticeConfiguration) (hE : MeasurableSet E) :
    (((boxProbabilityMeasure q (0, 0) r : ProbabilityMeasure LatticeConfiguration) E : NNReal) : ℝ) =
      FiniteProbability.expectation (law (boxGraph (0, 0) r) q (BoundaryCondition.free ∅))
        (Set.indicator ({A | boxConfiguration (0, 0) r A ∈ E} :
          Set (Configuration (boxGraph (0, 0) r))) (fun _ => (1 : ℝ))) := by
  have hpre :
      ((boxProbabilityMeasure q (0, 0) r : Measure LatticeConfiguration) E) =
        measure (boxGraph (0, 0) r) q (BoundaryCondition.free ∅)
          {A | boxConfiguration (0, 0) r A ∈ E} := by
    change ((law (boxGraph (0, 0) r) q (BoundaryCondition.free ∅)).map
      (boxConfiguration (0, 0) r)).toMeasure E = _
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
    rfl
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def]
  simp_all [fkLaw_measure_toReal_eq_expectation, BoundaryCondition.free]

/-- The free origin-box laws are increasing on every clopen increasing event
of the actual whole-lattice configuration space. -/
theorem boxProbabilityMeasure_clopen_upper_mono (r s : ℕ) (hrs : r ≤ s) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤ boxProbabilityMeasure q (0, 0) s E := by
  let f := boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  have hGH :=
    boxGraph_map_boxVertexEmbedding (latticeBox_mono (0, 0) hrs)
  let S :=
    {A | boxConfiguration (0, 0) r A ∈ E}
  let F :=
    S.indicator (fun _ => (1 : ℝ))
  have hF0 : ∀ A, 0 ≤ F A := by
    intro A
    by_cases hA : A ∈ S <;> simp [F, hA]
  have hF : Monotone F := by
    intro A B hAB
    by_cases hA : A ∈ S
    · have hB : B ∈ S := hEupper (boxConfiguration_mono (0, 0) r hAB)
        (by grind)
      simp [F, hA, hB]
    · simp only [F, Set.indicator_of_notMem hA]
      grind
  have hcmp := embedded_free_expectation_le (boxGraph (0, 0) r) (boxGraph (0, 0) s)
    f hGH q ∅ ∅ F hF0 hF
  have hrestrict :
      FiniteProbability.expectation (law (boxGraph (0, 0) s) q (BoundaryCondition.free ∅))
        (fun B => F (embeddedConfigurationRestriction (boxGraph (0, 0) r)
          (boxGraph (0, 0) s) f hGH B)) ≤
      FiniteProbability.expectation (law (boxGraph (0, 0) s) q (BoundaryCondition.free ∅))
        (Set.indicator ({B | boxConfiguration (0, 0) s B ∈ E} :
          Set (Configuration (boxGraph (0, 0) s))) (fun _ => (1 : ℝ))) := by
    apply FiniteProbability.expectation_mono
    intro B
    have horder := boxConfiguration_restriction_le hrs hGH B
    by_cases hsmall : boxConfiguration (0, 0) r
        (embeddedConfigurationRestriction (boxGraph (0, 0) r) (boxGraph (0, 0) s) f hGH B) ∈ E
    · simp [F, S, Set.indicator, hsmall, (hEupper horder hsmall)]
    · by_cases hlarge : boxConfiguration (0, 0) s B ∈ E <;>
        simp [F, S, Set.indicator, hsmall, hlarge]
  have hprob_r := boxProbabilityMeasure_event_eq_expectation q r E hEclopen.2.measurableSet
  have hprob_s := boxProbabilityMeasure_event_eq_expectation q s E hEclopen.2.measurableSet
  have hreal :
      (((boxProbabilityMeasure q (0, 0) r E : NNReal) : ℝ)) ≤
        (((boxProbabilityMeasure q (0, 0) s E : NNReal) : ℝ)) := by
    linarith
  exact NNReal.coe_le_coe.mp hreal

/-- Every finite free origin-box probability of a clopen increasing event is
bounded by its probability under the unique free infinite-volume limit. -/
theorem freeBoxLimit_clopen_upper_ge_box (r : ℕ) (E : Set LatticeConfiguration)
    (hEclopen : IsClopen E) (hEupper : IsUpperSet E) :
    boxProbabilityMeasure q (0, 0) r E ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)) E := by
  have hweak :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hnr : Tendsto (fun n : ℕ => n + r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hweakShift := hweak.comp hnr
  have hfixed (n : ℕ) :=
    boxProbabilityMeasure_clopen_upper_mono q r (n + r) (by omega) E hEclopen hEupper
  have hlim := le_of_tendsto_of_tendsto' tendsto_const_nhds (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweakShift hEclopen) hfixed
  omega
end

end
end PottsDiscontinuity.TorusLoops
