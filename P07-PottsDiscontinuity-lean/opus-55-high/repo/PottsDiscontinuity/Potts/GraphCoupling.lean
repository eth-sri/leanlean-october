module

public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.Potts.ClusterColoring
public import PottsDiscontinuity.Potts.FiniteExpansion

/-!
# Finite free Edwards–Sokal coupling

Open bonds enforce agreement of their endpoint colours. This is precisely
constancy on the actual connected components, including isolated vertices.
Counting these colourings identifies the bond marginal with the finite free
random-cluster law at `p = 1 - exp (-β)` and integer cluster weight `q`.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

variable {V C : Type*}

/-- The two endpoints of an edge have the same colour. -/
def edgeAgreement (G : SimpleGraph V) (σ : V → C) (e : G.edgeSet) : Prop :=
  ∀ x ∈ e.val, ∀ y ∈ e.val, σ x = σ y

/-- Open-edge agreement is exactly constancy on connected components. -/
theorem open_edgeAgreement_iff (G : SimpleGraph V) (A : FK.Configuration G) (σ : V → C) :
    (∀ e ∈ A, edgeAgreement G σ e) ↔
      (FK.openGraph G A).reachableSetoid ≤ Setoid.ker σ := by
  constructor
  · intro h
    apply FK.reachableSetoid_le_of_adj
    intro x y hxy
    rcases (FK.openGraph_adj G A x y).mp hxy with ⟨e, he, hexy⟩
    exact h e he x
      (by grind) y
      (by grind)
  · intro h e he x hx y hy
    by_cases hxy : x = y
    · simp_all
    · have ha :=
        (FK.openGraph_adj G A x y).mpr
          ⟨e, he, (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩⟩
      exact h ha.reachable

variable [Finite V] (G : SimpleGraph V)

local instance graphVertexFintype : Fintype V := Fintype.ofFinite _
local instance graphEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance graphEdgeDecidableEq : DecidableEq G.edgeSet :=
  fun _ _ => Classical.propDecidable _

theorem bool_edgeAgreement_iff (σ : V → C) (ω : G.edgeSet → Bool) :
    (∀ e, ω e = true → edgeAgreement G σ e) ↔
      (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid ≤ Setoid.ker σ := by
  simpa only [FK.mem_boolConfigurationEquiv] using
    open_edgeAgreement_iff G (FK.boolConfigurationEquiv G ω) σ

/-- There is one independent colour choice per actual open component. -/
theorem card_edgeAgreement (ω : G.edgeSet → Bool) :
    Nat.card {σ : V → C // ∀ e, ω e = true → edgeAgreement G σ e} =
      Nat.card C ^ FK.componentCount G (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv G ω) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun σ => bool_edgeAgreement_iff G σ ω)), card_clusterColoring, FK.componentCount, FK.componentSetoid_free]

@[simp] theorem card_pottsColors (q : ℕ) : Nat.card (Set.Icc 1 q) = q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_Icc, Nat.card_Icc]
  omega

section
variable (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
include q hq hβ
/-- The free random-cluster weight is the Bernoulli bond weight times the
number of compatible Potts colourings. -/
theorem fk_weight_eq_bernoulli (ω : G.edgeSet → Bool) :
    FK.weight G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv G ω) =
      bernoulliBondWeight β ω * (q : ℝ) ^
        FK.componentCount G (FK.BoundaryCondition.free ∅) (FK.boolConfigurationEquiv G ω) := by
  rw [bernoulliBondWeight_eq, FK.weight, FK.card_boolConfigurationEquiv,
    FK.closed_card_boolConfigurationEquiv, FK.card_boolConfigurationEquiv]
  rfl

/-- Summing the spin variable gives exactly the free random-cluster weight. -/
theorem sum_graphJointWeight_spins (ω : G.edgeSet → Bool) :
    (∑ σ : V → Set.Icc 1 q, constraintJointWeight β (edgeAgreement G) σ ω) =
      FK.weight G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv G ω) := by
  rw [sum_constraintJointWeight_spins, card_edgeAgreement, card_pottsColors,
    fk_weight_eq_bernoulli, Nat.cast_pow]

/-- The joint spin-bond partition function is exactly the FK partition function. -/
theorem graphJointPartition_eq_fk  :
    constraintJointPartition β (edgeAgreement G (C := Set.Icc 1 q)) =
      FK.partitionFunction G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅) := by
  unfold constraintJointPartition
  rw [Finset.sum_comm]
  simp_rw [sum_graphJointWeight_spins G q hq β hβ]
  exact (FK.boolConfigurationEquiv G).sum_comp _

/-- The joint weight factors into the FK weight and the probability of the
given colouring under independent uniform colours on open components. -/
theorem graphJointWeight_eq_fk_mul_coloring
    (σ : V → Set.Icc 1 q) (ω : G.edgeSet → Bool) :
    constraintJointWeight β (edgeAgreement G) σ ω =
      FK.weight G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv G ω) *
      clusterColoringProbability
        (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid σ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rw [constraintJointWeight_eq, fk_weight_eq_bernoulli, clusterColoringProbability]
  simp only [bool_edgeAgreement_iff, card_pottsColors, FK.componentCount,
    FK.componentSetoid_free]
  simp_all

/-- Finite Edwards–Sokal disintegration: conditionally on the bonds, each
actual connected component receives one independent uniform colour. -/
theorem graphJointProbability_eq_fk_mul_coloring
    (σ : V → Set.Icc 1 q) (ω : G.edgeSet → Bool) :
    constraintJointProbability β (edgeAgreement G) σ ω =
      FK.configurationProbability G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv G ω) *
      clusterColoringProbability
        (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid σ := by
  grind [constraintJointProbability, graphJointWeight_eq_fk_mul_coloring, graphJointPartition_eq_fk, FK.configurationProbability]

/-- The finite free Gibbs spin law is the mixture of uniform component
colourings against the actual finite free FK law. -/
theorem graphGibbsProbability_eq_clusterMixture
    (σ : V → Set.Icc 1 q) :
    constraintGibbsWeight β (edgeAgreement G) σ /
        ∑ τ : V → Set.Icc 1 q, constraintGibbsWeight β (edgeAgreement G) τ =
      ∑ ω : G.edgeSet → Bool,
        FK.configurationProbability G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
          (FK.boolConfigurationEquiv G ω) *
        clusterColoringProbability
          (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid σ := by
  let : Nonempty (Set.Icc 1 q) := by aesop
  rw [← constraintJointProbability_spin_marginal β (edgeAgreement G) σ]
  simp_all [graphJointProbability_eq_fk_mul_coloring]

/-- Every finite spin event, in particular every spin cylinder, is given by
the corresponding mixture of component-colouring probabilities. -/
theorem graphGibbsProbability_event_eq_clusterMixture
    (s : Set (V → Set.Icc 1 q)) :
    (∑ σ : V → Set.Icc 1 q,
      if σ ∈ s then constraintGibbsWeight β (edgeAgreement G) σ /
        (∑ τ : V → Set.Icc 1 q, constraintGibbsWeight β (edgeAgreement G) τ) else 0) =
      ∑ ω : G.edgeSet → Bool,
        FK.configurationProbability G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
          (FK.boolConfigurationEquiv G ω) *
        ∑ σ : V → Set.Icc 1 q,
          if σ ∈ s then clusterColoringProbability
            (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid σ else 0 := by
  simp_rw [graphGibbsProbability_eq_clusterMixture G q hq β hβ]
  calc
    _ = ∑ σ : V → Set.Icc 1 q, ∑ ω : G.edgeSet → Bool,
        FK.configurationProbability G (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
          (FK.boolConfigurationEquiv G ω) *
        (if σ ∈ s then clusterColoringProbability
          (FK.openGraph G (FK.boolConfigurationEquiv G ω)).reachableSetoid σ else 0) := by
      simp
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
end

end

end PottsDiscontinuity.Potts
