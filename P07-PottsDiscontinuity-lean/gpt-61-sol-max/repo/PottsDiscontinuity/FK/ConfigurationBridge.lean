module
public import Mathlib

public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.Frozen.Defs.RCFreeClusterCount

/-!
# Boolean configurations and finite open-edge sets

These equivalences preserve the actual open graph and both edge counts. They
connect the frozen Boolean carrier to the finite-set carrier of the FK core.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance configurationBridgeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- A Boolean configuration is identified with its set of open edges. -/
def boolConfigurationEquiv : (G.edgeSet → Bool) ≃ Configuration G := by
  classical
  exact
    { toFun := fun ω => Finset.univ.filter  fun e => ω e = true 
      invFun := fun A e => decide (e ∈ A)
      left_inv := by
        grind
      right_inv := by
        intro A
        ext e
        simp }

section

variable (ω : G.edgeSet → Bool)


@[simp] theorem mem_boolConfigurationEquiv  (e : G.edgeSet) :
    e ∈ boolConfigurationEquiv G ω ↔ ω e = true := by
  
  simp [boolConfigurationEquiv]

@[simp] theorem card_boolConfigurationEquiv  :
    (boolConfigurationEquiv G ω).card = Nat.card {e // ω e = true} := by
  
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem closed_card_boolConfigurationEquiv  :
    Nat.card {e // ω e = false} =
      Nat.card G.edgeSet - (boolConfigurationEquiv G ω).card := by
  
  rw [card_boolConfigurationEquiv]
  simp only [Bool.eq_false_iff, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

theorem openEdges_boolConfigurationEquiv  :
    openEdges G (boolConfigurationEquiv G ω) =
      {e | ∃ h : e ∈ G.edgeSet, ω ⟨e, h⟩ = true} := by
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    simp_all
  · rintro ⟨h, hω⟩
    exact ⟨⟨e, h⟩, (mem_boolConfigurationEquiv G ω ⟨e, h⟩).mpr hω, rfl⟩

theorem openGraph_boolConfigurationEquiv  :
    openGraph G (boolConfigurationEquiv G ω) =
      SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, ω ⟨e, h⟩ = true} := by
  rw [openGraph, openEdges_boolConfigurationEquiv]

end

/-- The two configuration carriers give exactly the same frozen open graph. -/
theorem rcOpenGraph_eq (S : Finset (ℤ × ℤ))
    (ω : (PottsDiscontinuity.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    openGraph _ (boolConfigurationEquiv _ ω) = rcOpenGraph S ω :=
  openGraph_boolConfigurationEquiv _ ω

/-- Free wiring counts precisely the frozen connected components, including
isolated vertices. -/
theorem componentCount_free_eq_rcFreeClusterCount (S : Finset (ℤ × ℤ))
    (B : Set (S : Set (ℤ × ℤ)))
    (ω : (PottsDiscontinuity.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    componentCount _ (BoundaryCondition.free B) (boolConfigurationEquiv _ ω) =
      rcFreeClusterCount S ω := by
  rw [componentCount, componentSetoid_free, rcOpenGraph_eq]
  rfl

end

end PottsDiscontinuity.FK
