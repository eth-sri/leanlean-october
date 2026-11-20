module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DualCylinderLaw
public import PottsDiscontinuity.Duality.WiredDomainLimit
public import PottsDiscontinuity.FK.FreeBoxLimitV1

/-! Infinite-volume free/wired duality for the actual frozen box limits. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial MeasureTheory Filter Topology
noncomputable section

variable (q : Set.Ici (1 : ℝ)) {θ : Parameters} (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (n : ℕ)

include n in
/-- Lower left corner of the origin-centered primal box. -/
def originBoxAnchor : LatticeVertex := (-n, -n)

lemma originBoxRectangle_eq :
    latticeRectangle (originBoxAnchor n) (2 * n) (2 * n) = box n := by
  simpa only [originBoxAnchor, zero_sub, Prod.fst_zero, Prod.snd_zero] using
    (latticeRectangle_box_eq _ n).trans (latticeBox_origin_eq_box n)

/-- Every fixed original lattice edge eventually belongs to the genuine dual
edge carrier, rather than merely to the larger ambient induced graph. -/
lemma eventually_edge_in_trueDual (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop, e ∈ Set.range
      (rectangleDualEdgeToSquareEdge (originBoxAnchor n) (2 * n) (2 * n)) := by
  filter_upwards [eventually_edge_lift_box _] with n hn
  rw [← originBoxRectangle_eq n] at hn
  obtain ⟨f, hf⟩ := hn
  let d := rectanglePrimalDualEdgeEquiv _ _ _ f
  refine ⟨rectangleDualGraphEdgeEquiv _ _ _ d, ?_⟩
  apply wholePlaneDualCrossingEdgeEquiv.injective
  have he : wholePlaneDualCrossingEdgeEquiv
      (rectangleDualEdgeToSquareEdge (originBoxAnchor n) (2 * n) (2 * n)
        (rectangleDualGraphEdgeEquiv _ _ _ d)) =
      rectanglePrimalEdgeToSquareEdge f := by
    change wholePlaneBondEdgeEquiv (primalBondOfDual
      (wholePlaneBondEdgeEquiv.symm (wholePlaneBondEdgeEquiv d.crossingBond))) = _
    rw [Equiv.symm_apply_apply]
    exact rectangleDualEdge_crossing_originalEdge _ _ _ d
  rw [he]
  exact Subtype.ext hf

lemma dualExpanded_origin_inner :
    latticeBox (0, 0) n ⊆ rectangleDualExpanded (originBoxAnchor n) (2 * n) (2 * n) := by
  intro x hx
  simp only [mem_latticeBox, rectangleDualExpanded, mem_latticeRectangle,
    originBoxAnchor, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hx ⊢
  omega

lemma dualExpanded_origin_outer :
    rectangleDualExpanded (originBoxAnchor n) (2 * n) (2 * n) ⊆
      latticeBox (0, 0) (n + 1) := by
  intro x hx
  simp only [mem_latticeBox, rectangleDualExpanded, mem_latticeRectangle,
    originBoxAnchor, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hx ⊢
  omega

/-- The actual whole-plane dual transform pushes the frozen free measure at p
to the frozen wired measure at p*, for arbitrary interior p and q ≥ 1. -/
theorem free_map_dual_eq_wired
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₀.map wholePlaneDualConfigurationHomeomorph = μ₁ := by
  let ν₀ : ProbabilityMeasure LatticeConfiguration := ⟨μ₀, hμ₀.1⟩
  obtain ⟨ν, hν, _⟩ := freeBoxLimit_existsUnique θ
  have hνorigin := hν _ _
    origin_latticeBox_nested origin_latticeBox_exhaustive
  have heq : ν₀ = ν := ProbabilityMeasure.toMeasure_injective
    (rc_limit_unique hμ₀
      (isRCInfiniteVolumeLimit_of_freeBox_tendsto hνorigin))
  have hfree : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 ν₀) := by
    grind
  have hdual := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hfree
    wholePlaneDualConfigurationHomeomorph.continuous
  have hprob : ν₀.map wholePlaneDualConfigurationHomeomorph = ⟨μ₁, hμ₁.1⟩ := by
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    have h₁ := LatticeConfiguration.tendsto_allOpen_of_weak (wiredDomainProbabilityMeasure_tendsto_of_box_sandwich μ₁ hμ₁ dualExpanded_origin_inner dualExpanded_origin_outer) F
    apply tendsto_nhds_unique (LatticeConfiguration.tendsto_allOpen_of_weak hdual F)
    apply h₁.congr'
    filter_upwards [((eventually_all_finset F).2 fun e _ => eventually_edge_in_trueDual e)] with n hn
    apply ENNReal.coe_injective
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    have h := freeRectangle_dual_allOpen θ F hn
    have hb : freeRectangleProbabilityMeasure θ (originBoxAnchor n) (2 * n) (2 * n) =
        boxProbabilityMeasure θ (0, 0) n := by
      simpa only [originBoxAnchor, Prod.fst_zero, Prod.snd_zero, zero_sub] using
        freeRectangleProbabilityMeasure_box θ (0, 0) n
    rw [hb] at h
    exact h.symm
  exact congrArg ProbabilityMeasure.toMeasure hprob

end
end PottsDiscontinuity.Duality
