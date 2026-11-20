/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCompactness
public import PottsDiscontinuity.FK.Isomorphism
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsDiscontinuity.FK
open MeasureTheory
noncomputable section
/-- Isometries preserving box membership restrict to the finite induced graphs. -/
def boxGraphIsoOfLatticeIso (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) : boxGraph c r ≃g boxGraph (e c) r where
  toEquiv := e.toEquiv.subtypeEquiv (fun v => (hbox c v r).symm)
  map_rel_iff' := e.map_rel_iff'

/-- Transport an edge state along a lattice isomorphism. -/
def latticeConfigurationIsoHomeomorph (e : squareLattice ≃g squareLattice) :
    LatticeConfiguration ≃ₜ LatticeConfiguration :=
  Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet e)

@[simp] theorem latticeConfigurationIsoHomeomorph_apply
    (e : squareLattice ≃g squareLattice) (ω : LatticeConfiguration) (b : squareLattice.edgeSet) :
    latticeConfigurationIsoHomeomorph e ω b = ω (SimpleGraph.Iso.mapEdgeSet e.symm b) := by
  simp [latticeConfigurationIsoHomeomorph, Homeomorph.piCongrLeft, Equiv.piCongrLeft]

theorem latticeConfigurationIsoHomeomorph_measurable (e : squareLattice ≃g squareLattice) :
    Measurable (latticeConfigurationIsoHomeomorph e) :=
  (latticeConfigurationIsoHomeomorph e).continuous.measurable

section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem boundaryConditionIso_free_empty (e : G ≃g H) :
    boundaryConditionIso e (BoundaryCondition.free (∅ : Set V)) =
      BoundaryCondition.free (∅ : Set W) := by
  cases e
  simp only [boundaryConditionIso, BoundaryCondition.free, Setoid.comap]
  congr 1
  · simp
  · apply Setoid.ext
    simp

end

def latticeConfigurationTranslationHomeomorph (a : LatticeVertex) :
    LatticeConfiguration ≃ₜ LatticeConfiguration :=
  latticeConfigurationIsoHomeomorph (latticeTranslationIso a)

def latticeConfigurationTranslate (a : LatticeVertex) : LatticeConfiguration ≃ LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph a).toEquiv

theorem latticeConfigurationTranslate_measurable (a : LatticeVertex) :
    Measurable (latticeConfigurationTranslate a) :=
  (latticeConfigurationTranslationHomeomorph a).continuous_toFun.measurable

@[simp] theorem latticeConfigurationTranslate_apply (a : LatticeVertex)
    (ω : LatticeConfiguration) (b : squareLattice.edgeSet) :
    latticeConfigurationTranslate a ω b =
      ω (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) b) := by
  simp [latticeConfigurationTranslate, latticeConfigurationTranslationHomeomorph, SimpleGraph.Hom.mapEdgeSet, latticeTranslationIso]

lemma boxEdgeEmbedding_iso_commute
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) (b : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding (e c) r
        (SimpleGraph.Iso.mapEdgeSet (boxGraphIsoOfLatticeIso e hbox c r) b) =
      SimpleGraph.Iso.mapEdgeSet e (boxEdgeEmbedding c r b) := by
  apply Subtype.ext
  simp only [boxEdgeEmbedding, boxGraphEmbedding,
    SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Iso.mapEdgeSet_apply,
    SimpleGraph.Hom.mapEdgeSet_coe, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding]
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

section Transport

variable (e : squareLattice ≃g squareLattice)
  (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
  (c : LatticeVertex) (r : ℕ)

/-- The extension commutes with transport: at an embedded edge use its finite
state, and otherwise use the common exterior state. -/
theorem boxExtension_iso_commute
    (F : (a : LatticeVertex) → (s : ℕ) → Configuration (boxGraph a s) → LatticeConfiguration)
    (z : Bool)
    (hin : ∀ a s A b, F a s A (boxEdgeEmbedding a s b) = decide (b ∈ A))
    (hout : ∀ a s A b, b ∉ Set.range (boxEdgeEmbedding a s) → F a s A b = z)
    (A : Configuration (boxGraph c r)) :
    F (e c) r (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A) =
      latticeConfigurationIsoHomeomorph e (F c r A) := by
  let E := SimpleGraph.Iso.mapEdgeSet e
  let I := SimpleGraph.Iso.mapEdgeSet (boxGraphIsoOfLatticeIso e hbox c r)
  funext b
  obtain ⟨b, rfl⟩ := E.surjective b
  rw [latticeConfigurationIsoHomeomorph, Homeomorph.piCongrLeft_apply_apply]
  by_cases hb : b ∈ Set.range (boxEdgeEmbedding c r)
  · obtain ⟨b, rfl⟩ := hb
    rw [← boxEdgeEmbedding_iso_commute e hbox, hin, hin]
    change decide (I b ∈ A.map I.toEmbedding) = decide (b ∈ A)
    simp
  · rw [hout _ _ _ _ hb, hout]
    rintro ⟨b', hb'⟩
    obtain ⟨x, rfl⟩ := I.surjective b'
    exact hb ⟨x, E.injective ((boxEdgeEmbedding_iso_commute e hbox c r x).symm.trans hb')⟩

/-- Transport the FK law and its extension together. The boundary partition
is the only boundary datum needed by the finite law. -/
theorem boxLaw_iso_map_of_commute (q : Parameters)
    (ξ : BoundaryCondition (BoxVertex c r)) (η : BoundaryCondition (BoxVertex (e c) r))
    (hξ : (boundaryConditionIso (boxGraphIsoOfLatticeIso e hbox c r) ξ).partition = η.partition)
    (F : Configuration (boxGraph c r) → LatticeConfiguration)
    (F' : Configuration (boxGraph (e c) r) → LatticeConfiguration)
    (hF : ∀ A, F' (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A) =
      latticeConfigurationIsoHomeomorph e (F A)) :
    ((law (boxGraph c r) q ξ).map F).map (latticeConfigurationIsoHomeomorph e) =
      (law (boxGraph (e c) r) q η).map F' := by
  rw [PMF.map_comp, show (latticeConfigurationIsoHomeomorph e : LatticeConfiguration → _) ∘ F =
      F' ∘ configurationIso (boxGraphIsoOfLatticeIso e hbox c r) from funext fun A => (hF A).symm,
    ← PMF.map_comp, law_configurationIso_map, law_eq_of_boundary_partition_eq q _ _ hξ]

end Transport

theorem probabilityMeasureMap_eq_of_PMF {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : PMF Ω} {f : Ω → Ω} (hf : Measurable f) (h : μ.map f = ν) :
    ProbabilityMeasure.map ⟨μ.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩ f =
      ⟨ν.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map f μ.toMeasure = ν.toMeasure
  rw [PMF.toMeasure_map _ _ hf, h]

theorem boxProbabilityMeasure_iso_map (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure.map (boxProbabilityMeasure q c r) (latticeConfigurationIsoHomeomorph e) =
      boxProbabilityMeasure q (e c) r := by
  refine probabilityMeasureMap_eq_of_PMF (latticeConfigurationIsoHomeomorph e).continuous.measurable
    (boxLaw_iso_map_of_commute e hbox c r q _ _ ?_ _ _ ?_)
  · rw [boundaryConditionIso_free_empty]
  · exact boxExtension_iso_commute e hbox c r boxConfiguration false
      boxConfiguration_at boxConfiguration_outside

end
end PottsDiscontinuity.FK
