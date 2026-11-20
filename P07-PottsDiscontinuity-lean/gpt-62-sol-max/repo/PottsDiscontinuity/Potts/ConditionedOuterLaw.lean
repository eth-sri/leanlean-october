module

public import PottsDiscontinuity.Potts.GhostBoxCylinders
public import PottsDiscontinuity.Potts.FiniteConditioning
public import PottsDiscontinuity.Potts.ConditionedComparison
public import PottsDiscontinuity.Potts.GhostBoxContraction
public import PottsDiscontinuity.Infra.ClopenProbability

/-! The full conditioned outer law, including its boundary connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

 theorem cornerClosureEvent_support (θ : FK.Parameters) (n : ℕ) :
    ∃ C ∈ cornerClosureEvent n,
      C ∈ (FK.law (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) θ (outerBoxWiring n)).support := by
  refine ⟨∅, Finset.disjoint_empty_right _, ?_⟩
  exact (FK.law_pos _ θ (outerBoxWiring n) ∅).ne'

section

variable (θ : FK.Parameters) (n : ℕ)

/-- The actual outer FK law conditioned on the four closed corner bonds. -/
def conditionedOuterLaw :
    PMF (FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))) :=
  (FK.law _ θ (outerBoxWiring n)).filter (cornerClosureEvent n) (cornerClosureEvent_support θ n)

def conditionedOuterBoxProbabilityMeasure :
    ProbabilityMeasure FK.LatticeConfiguration :=
  ⟨((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

private theorem conditionedOuterBox_real
    (A : Set FK.LatticeConfiguration) (hA : MeasurableSet A) :
    (conditionedOuterBoxProbabilityMeasure θ n).toMeasure.real A =
      (FK.measure _ θ (outerBoxWiring n)
        (openExtension (box (n + 1)) ⁻¹' A ∩ cornerClosureEvent n)).toReal /
      (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal := by
  change (((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure A).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hA]
  exact finite_filter_measureReal ..

end

private theorem openBox_real (θ : FK.Parameters) (n : ℕ)
    {A : Set FK.LatticeConfiguration} (hA : MeasurableSet A) :
    (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real A =
      (FK.measure _ θ (outerBoxWiring n) (openExtension (box (n + 1)) ⁻¹' A)).toReal := by
  exact congrArg ENNReal.toReal (PMF.toMeasure_map_apply _ _ _ measurable_from_top hA)

private def cornerEvent (n : ℕ) : Set FK.LatticeConfiguration :=
  FK.patternCylinder ((cornerCutEdges n).map (FK.frozenEdgeEmbedding (box (n + 1)))) (fun _ => false)

private theorem preimage_cornerEvent (n : ℕ) :
    openExtension (box (n + 1)) ⁻¹' cornerEvent n = cornerClosureEvent n := by
  ext C
  simp only [Set.mem_preimage, cornerEvent, FK.patternCylinder, cornerClosureEvent, allClosedEdges,
    Set.mem_ofPred_eq, Finset.forall_mem_map, openExtension_at, decide_eq_false_iff_not,
    Finset.disjoint_left]

private theorem cornerEvent_outside (n : ℕ) :
    RCInfinite.DependsOn (RCInfinite.boxEdges (0, 0) n)ᶜ (cornerEvent n) := by
  intro ω η h
  simp only [cornerEvent, FK.patternCylinder, Set.mem_ofPred_eq, Finset.forall_mem_map]
  refine forall₂_congr fun f hf => ?_
  rw [h _ ?_]
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hf
  rintro ⟨g, hg⟩
  have hg' : Sym2.map Subtype.val g.val = s(cornerPoint n b, cornerOutwardPoint n b) :=
    congrArg Subtype.val hg
  obtain ⟨x, _, hx⟩ := Sym2.mem_map.mp (hg'.symm ▸ Sym2.mem_mk_right _ _)
  exact cornerOutwardPoint_not_mem n b (hx ▸ FK.latticeBox_origin_eq_box n ▸ x.property)

/-- The same domain-Markov comparison used for mixing also controls the corner correction. -/
private theorem conditioned_allOpen_bounds (θ : FK.Parameters) (n : ℕ) (hn : 0 < n)
    (F : Finset squareLattice.edgeSet) (hF : (F : Set _) ⊆ RCInfinite.boxEdges (0, 0) n) :
    let A := FK.LatticeConfiguration.allOpen F
    let u := (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real A
    let c := (openBoxProbabilityMeasure θ n).toMeasure.real A
    let g := (conditionedOuterBoxProbabilityMeasure θ n).toMeasure.real A
    u - (c - u) / (1 - FK.edgeParameter θ) ^ 4 ≤ g ∧ g ≤ u := by
  let A := FK.LatticeConfiguration.allOpen F
  let B := cornerEvent n
  have hA : MeasurableSet A := (FK.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet
  have hB : MeasurableSet B := (FK.patternCylinder_isClopen _ _).isOpen.measurableSet
  have hm := FK.origin_latticeBox_nested n
  have hc := RCInfinite.box_joint_compare θ 1 hm F hF Bᶜ hB.compl (cornerEvent_outside n).compl
  have hu := RCInfinite.box_joint_compare θ 1 hm F hF Set.univ MeasurableSet.univ (by simp [RCInfinite.DependsOn])
  simp only [RCInfinite.comparisonSign_one, one_mul, RCInfinite.boxMeasure_wired, ← openBoxProbabilityMeasure_eq_wired] at hc hu
  have h1 : (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real Set.univ = 1 := by simp
  simp only [Set.inter_univ, h1, mul_one] at hu
  rw [measureReal_compl hB, h1] at hc
  have hsplit := measureReal_inter_add_sdiff (μ := (openBoxProbabilityMeasure θ (n + 1)).toMeasure)
    (s := A) hB
  change _ + (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real (A ∩ Bᶜ) = _ at hsplit
  have ht := hsplit.ge.trans (add_le_add_right hc _)
  have hpre : openExtension (box (n + 1)) ⁻¹' A = openBoxCylinderEvent (n + 1) F :=
    Set.ext fun C => openExtension_mem_allOpen _ C F
  have hδ := pow_pos (FK.one_sub_edgeParameter_pos θ) 4
  have hb := cornerClosureEvent_probability_lower_bound θ n hn
  have hg := conditioned_decreasing_event_le θ (outerBoxWiring n) _ _ (openBoxCylinderEvent_upper _ F)
    (isLowerSet_allClosedEdges (cornerCutEdges n)) (hδ.trans_le hb)
  rw [openBox_real θ n (hA.inter hB), openBox_real θ n hB, Set.preimage_inter, hpre, preimage_cornerEvent] at ht
  have hu₀ := openBox_real θ n hA
  rw [hpre] at hu₀
  dsimp only
  rw [conditionedOuterBox_real _ _ _ hA, hpre]
  exact conditioned_ratio_squeeze_bounds hδ hb (hg.trans_eq hu₀.symm) hu ht

/-- The conditioned full outer laws have the same wired weak limit. -/
theorem conditionedOuterBox_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) :
    Tendsto (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ)) atTop (𝓝 μ) := by
  have hinj : Function.Injective FK.cylinderProbabilityCoordinates := by
    intro μ ν h
    exact FK.LatticeConfiguration.probabilityMeasure_eq_of_allOpen (fun F => congrFun h F)
  have hemb := FK.continuous_cylinderProbabilityCoordinates.isClosedEmbedding hinj
  apply hemb.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro F
  apply NNReal.tendsto_coe.mp
  let θ := fkParameters q hq β hβ
  let U n := (openBoxProbabilityMeasure θ n).toMeasure.real (FK.LatticeConfiguration.allOpen F)
  have hw : Tendsto U atTop (𝓝 (μ.toMeasure.real (FK.LatticeConfiguration.allOpen F))) := by
    simpa only [U, openBoxProbabilityMeasure_eq_wired] using
      ProbabilityMeasure.tendsto_real_clopen hμ (FK.LatticeConfiguration.allOpen_isClopen F)
  have hu := hw.comp (tendsto_add_atTop_nat 1)
  have hl := hu.sub ((hw.sub hu).div_const ((1 - FK.edgeParameter θ) ^ 4))
  simp only [sub_self, zero_div, sub_zero] at hl
  have hlarge : ∀ᶠ n : ℕ in atTop, (F : Set _) ⊆ RCInfinite.boxEdges (0, 0) n :=
    (eventually_all_finset F).mpr (fun e _ => (FK.eventually_edge_lift_box e).mono fun n ⟨f, hf⟩ =>
      boxEdges_origin_eq_range n ▸ ⟨f, Subtype.ext hf⟩) |>.mono fun _ h e he => h e he
  have hb := ((eventually_gt_atTop 0).and hlarge).mono fun n ⟨hn, hF⟩ => conditioned_allOpen_bounds θ n hn F hF
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- The conditional density is bounded by the reciprocal of the four-edge
finite-energy constant, uniformly in the volume. -/
theorem conditionedOuterLaw_density (θ : FK.Parameters) (n : ℕ) (hn : 0 < n)
    (S : Set (FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))))) :
    (1 - FK.edgeParameter θ) ^ 4 * (conditionedOuterLaw θ n).toMeasure.real S ≤
      (FK.measure _ θ (outerBoxWiring n) S).toReal := by
  change (1 - FK.edgeParameter θ) ^ 4 *
    ((FK.law _ θ (outerBoxWiring n)).filter _ _).toMeasure.real S ≤ _
  rw [finite_filter_measureReal]
  have hb := cornerClosureEvent_probability_lower_bound θ n hn
  have hbpos : 0 < (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal :=
    (pow_pos (FK.one_sub_edgeParameter_pos θ) 4).trans_le hb
  have ha : 0 ≤ (FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal /
      (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal :=
    div_nonneg ENNReal.toReal_nonneg hbpos.le
  calc
    _ ≤ (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal *
        ((FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal /
          (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal) :=
      mul_le_mul_of_nonneg_right hb ha
    _ = (FK.measure _ θ (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal := by
      rw [mul_comm, div_mul_cancel₀ _ hbpos.ne']
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)

theorem conditionedOuterBox_density (θ : FK.Parameters) (n : ℕ) (hn : 0 < n)
    (S : Set FK.LatticeConfiguration) (hS : MeasurableSet S) :
    (1 - FK.edgeParameter θ) ^ 4 * (conditionedOuterBoxProbabilityMeasure θ n).toMeasure.real S ≤
      (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real S := by
  change (1 - FK.edgeParameter θ) ^ 4 *
    (((conditionedOuterLaw θ n).map (openExtension (box (n + 1)))).toMeasure S).toReal ≤
      (((FK.law _ θ (outerBoxWiring n)).map (openExtension (box (n + 1)))).toMeasure S).toReal
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hS,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top hS]
  exact conditionedOuterLaw_density θ n hn _

end
end PottsDiscontinuity.Potts
