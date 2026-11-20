module

public import PottsDiscontinuity.FK.Model
public import PottsDiscontinuity.FK.ConfigurationBridge
public import PottsDiscontinuity.FK.WiredComponentBridge
public import PottsDiscontinuity.Frozen.Defs.RCProb

/-!
# Exact finite-volume bridge to the frozen random-cluster probabilities

The graph is the frozen induced graph. Both boundary conditions use its entire
vertex carrier, so isolated vertices and boundary components are retained.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

section
variable (θ : Parameters) (S : Finset (ℤ × ℤ)) (i : Fin 2)
    (ω : (PottsDiscontinuity.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool)

include θ in
/-- The admissible closed-interval edge parameter of an interior FK model. -/
def Parameters.toP : Set.Icc (0 : ℝ) 1 :=
  ⟨edgeParameter θ, (edgeParameter_pos θ).le, (edgeParameter_lt_one θ).le⟩

include θ in
/-- The positive cluster parameter of an FK model with cluster weight at least one. -/
def Parameters.toQ : Set.Ioi (0 : ℝ) :=
  ⟨θ.val, clusterWeight_pos θ⟩

/-- The frozen vertex boundary, as a subset of the finite vertex carrier. -/
def frozenVertexBoundary : Set (S : Set (ℤ × ℤ)) :=
  {x | x.val ∈ vertexBoundary S}

include i in
/-- Free or wired boundary conditions, with exactly the frozen boundary vertices. -/
def frozenBoundaryCondition :
    BoundaryCondition (S : Set (ℤ × ℤ)) :=
  if i = 0 then BoundaryCondition.free (frozenVertexBoundary S)
  else BoundaryCondition.wired (frozenVertexBoundary S)

theorem componentCount_wired_eq_rcWiredClusterCount :
    componentCount (BoundaryCondition.wired (frozenVertexBoundary S))
      (boolConfigurationEquiv _ ω) = rcWiredClusterCount S ω := by
  classical
  rw [componentCount_wired_eq_boundary_avoiding, rcOpenGraph_eq]
  congr 1
  exact @ite_cond_congr ℕ _ _ _ _ 1 0 rfl

theorem componentCount_frozenBoundaryCondition :
    componentCount (frozenBoundaryCondition S i) (boolConfigurationEquiv _ ω) =
      if i = 0 then rcFreeClusterCount S ω else rcWiredClusterCount S ω := by
  unfold frozenBoundaryCondition
  split
  · exact componentCount_free_eq_rcFreeClusterCount S _ ω
  · exact componentCount_wired_eq_rcWiredClusterCount S ω

/-- The ported weight is exactly the frozen weight on the corresponding configuration. -/
theorem weight_eq_rcWeight :
    weight _ θ (frozenBoundaryCondition S i) (boolConfigurationEquiv _ ω) =
      rcWeight S (edgeParameter θ) θ.val i ω := by
  unfold weight rcWeight
  rw [componentCount_frozenBoundaryCondition,
    ← closed_card_boolConfigurationEquiv, card_boolConfigurationEquiv]

end

open Classical in
/-- The two finite partition functions are equal, without any normalization factor. -/
theorem partitionFunction_eq_rcPartition (θ : Parameters) (S : Finset (ℤ × ℤ))
    (i : Fin 2) :
    partitionFunction (PottsDiscontinuity.squareLattice.induce
      (S : Set (ℤ × ℤ))) θ (frozenBoundaryCondition S i) =
      ∑ ω, rcWeight S (edgeParameter θ) θ.val i ω := by
  symm
  refine Finset.sum_bij (fun ω _ => boolConfigurationEquiv _ ω) ?_ ?_ ?_ ?_
  · grind
  · simp_all
  · intro A _
    refine ⟨(boolConfigurationEquiv _).symm A, ?_,
      (boolConfigurationEquiv _).apply_symm_apply A⟩
    simp
  · intro ω _
    exact (weight_eq_rcWeight θ S i ω).symm

/-- Exact normalized probability bridge for arbitrary finite induced domains. -/
theorem configurationProbability_eq_rcProb (θ : Parameters) {S : Finset (ℤ × ℤ)}
    (i : Fin 2)
    (ω : (PottsDiscontinuity.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    configurationProbability _ θ (frozenBoundaryCondition S i)
      (boolConfigurationEquiv _ ω) = rcProb S θ.toP θ.toQ i ω := by
  unfold configurationProbability rcProb
  rw [weight_eq_rcWeight, partitionFunction_eq_rcPartition]
  rfl

end

end PottsDiscontinuity.FK
