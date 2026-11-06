/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.BoxTranslation

@[expose] public section

namespace PottsDiscontinuity.FK
open MeasureTheory
noncomputable section

/-- The literal counterclockwise quarter-turn `(x,y) ↦ (-y,x)`. -/
def latticeQuarterTurn (v : LatticeVertex) : LatticeVertex := (-v.2, v.1)

/-- The inverse quarter-turn `(x,y) ↦ (y,-x)`. -/
def latticeQuarterTurnInv (v : LatticeVertex) : LatticeVertex := (v.2, -v.1)



@[simp] theorem latticeQuarterTurnInv_quarterTurn (v : LatticeVertex) :
    latticeQuarterTurnInv (latticeQuarterTurn v) = v := by
  grind +locals

@[simp] theorem latticeQuarterTurn_quarterTurnInv (v : LatticeVertex) :
    latticeQuarterTurn (latticeQuarterTurnInv v) = v := by
  grind +locals



lemma squareLattice_adj_quarterTurn_iff (u v : LatticeVertex) :
    squareLattice.Adj (latticeQuarterTurn u) (latticeQuarterTurn v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeQuarterTurn]
  omega

/-- The actual graph isomorphism for the literal quarter-turn. -/
def latticeQuarterTurnIso : squareLattice ≃g squareLattice where
  toFun := latticeQuarterTurn
  invFun := latticeQuarterTurnInv
  left_inv := latticeQuarterTurnInv_quarterTurn
  right_inv := latticeQuarterTurn_quarterTurnInv
  map_rel_iff' := by
    simp_all [squareLattice_adj_quarterTurn_iff]

lemma mem_latticeBox_quarterTurn_iff (c v : LatticeVertex) (r : ℕ) :
    latticeQuarterTurn v ∈ latticeBox (latticeQuarterTurn c) r ↔
      v ∈ latticeBox c r := by
  rw [mem_latticeBox, mem_latticeBox]
  simp only [latticeQuarterTurn]
  omega

/-- A graph isomorphism preserving the lattice boxes induces the corresponding
finite induced-graph isomorphism. -/
def boxGraphIsoOfLatticeIso
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) : boxGraph c r ≃g boxGraph (e c) r where
  toEquiv :=
    { toFun := fun v => ⟨e v.1, (hbox c v.1 r).2 v.2⟩
      invFun := fun v => ⟨e.symm v.1, by
        have hv : e (e.symm v.1) ∈ latticeBox (e c) r := by simp
        all_goals grind⟩
      left_inv := fun v => Subtype.ext (e.left_inv ↑v)
      right_inv := fun v => Subtype.ext (e.right_inv ↑v) }
  map_rel_iff' := fun {u v} => e.map_rel_iff'

/-- Push configurations on the whole lattice along the original-edge map of a
lattice graph isomorphism. -/
def latticeConfigurationIsoHomeomorph (e : squareLattice ≃g squareLattice) :
    LatticeConfiguration ≃ₜ LatticeConfiguration :=
  Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet e)

section

variable (e : squareLattice ≃g squareLattice)
include e

@[simp] theorem latticeConfigurationIsoHomeomorph_apply
     (ω : LatticeConfiguration)
    (b : squareLattice.edgeSet) :
    latticeConfigurationIsoHomeomorph e ω b =
      ω (SimpleGraph.Iso.mapEdgeSet e.symm b) := by
  simp [latticeConfigurationIsoHomeomorph, Homeomorph.piCongrLeft, Equiv.piCongrLeft]

theorem latticeConfigurationIsoHomeomorph_measurable
     :
    Measurable (latticeConfigurationIsoHomeomorph e) :=
  (latticeConfigurationIsoHomeomorph e).continuous_toFun.measurable

section

variable (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) (c : LatticeVertex) (r : ℕ)


lemma boxEdgeEmbedding_iso_commute
    
     (b : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding (e c) r
        (SimpleGraph.Iso.mapEdgeSet (boxGraphIsoOfLatticeIso e hbox c r) b) =
      SimpleGraph.Iso.mapEdgeSet e (boxEdgeEmbedding c r b) := by
  apply Subtype.ext
  simp only [boxEdgeEmbedding, SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe]
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

lemma boxEmbeddedEdgeSet_iso_commute
    
     (A : Configuration (boxGraph c r)) :
    (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A).map
      (boxEdgeEmbedding (e c) r) =
      (A.map (boxEdgeEmbedding c r)).map
        (SimpleGraph.Iso.mapEdgeSet e).toEmbedding := by
  change (A.map (configurationIsoEdgeEquiv (boxGraphIsoOfLatticeIso e hbox c r)).toEmbedding).map
      (boxEdgeEmbedding (e c) r) =
    (A.map (boxEdgeEmbedding c r)).map
      (SimpleGraph.Iso.mapEdgeSet e).toEmbedding
  rw [Finset.map_map, Finset.map_map]
  have hEmb :
      (configurationIsoEdgeEquiv (boxGraphIsoOfLatticeIso e hbox c r)).toEmbedding.trans
          (boxEdgeEmbedding (e c) r) =
        (boxEdgeEmbedding c r).trans
          (SimpleGraph.Iso.mapEdgeSet e).toEmbedding := Function.Embedding.ext (boxEdgeEmbedding_iso_commute e hbox c r)
  rw [hEmb]

theorem boxConfiguration_iso_commute
    
     (A : Configuration (boxGraph c r)) :
    boxConfiguration (e c) r (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A) =
      latticeConfigurationIsoHomeomorph e (boxConfiguration c r A) := by
  funext b
  simp only [boxConfiguration, latticeConfigurationIsoHomeomorph_apply]
  
  
  rw [boxEmbeddedEdgeSet_iso_commute]
  
  simp [SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet]

end

end

section

variable (q : Parameters) (e : squareLattice ≃g squareLattice) (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) (c : LatticeVertex) (r : ℕ)
include hbox

theorem boxLaw_iso_map
     :
    PMF.map (latticeConfigurationIsoHomeomorph e).toEquiv (boxLaw q c r) =
      boxLaw q (e c) r := by
  rw [boxLaw, boxLaw, PMF.map_comp]
  have hcomp :
      (latticeConfigurationIsoHomeomorph e).toEquiv ∘ boxConfiguration c r =
        boxConfiguration (e c) r ∘ configurationIso (boxGraphIsoOfLatticeIso e hbox c r) := by
    funext A
    exact (boxConfiguration_iso_commute e hbox c r A).symm
  rw [hcomp, ← PMF.map_comp]
  rw [law_configurationIso_map q (boxGraphIsoOfLatticeIso e hbox c r)
      (BoundaryCondition.free ∅)]
  rw [boundaryConditionIso_free_empty]

theorem boxProbabilityMeasure_iso_map
     :
    ProbabilityMeasure.map (boxProbabilityMeasure q c r)
      (latticeConfigurationIsoHomeomorph e) =
        boxProbabilityMeasure q (e c) r := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (latticeConfigurationIsoHomeomorph e) (boxLaw q c r).toMeasure =
    (boxLaw q (e c) r).toMeasure
  rw [PMF.toMeasure_map _ _ (latticeConfigurationIsoHomeomorph_measurable e)]
  exact congrArg PMF.toMeasure (boxLaw_iso_map q e hbox c r)

end

end
end PottsDiscontinuity.FK

