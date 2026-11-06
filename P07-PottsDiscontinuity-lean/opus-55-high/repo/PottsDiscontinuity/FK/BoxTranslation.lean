/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCompactness
public import PottsDiscontinuity.FK.Isomorphism

@[expose] public section

namespace PottsDiscontinuity.FK
open MeasureTheory
noncomputable section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Translation identifies every vertex of a finite lattice box with the
corresponding vertex in the translated-center box. -/
def boxVertexTranslationIso (a c : LatticeVertex) (r : ℕ) :
    boxGraph c r ≃g boxGraph (latticeTranslate a c) r where
  toEquiv :=
    { toFun := fun v => ⟨latticeTranslate a v.val,
        (mem_latticeBox_translate_iff a c v.val r).mpr v.property⟩
      invFun := fun v => ⟨latticeTranslate (-a) v.val,
        by
          have h := (mem_latticeBox_translate_iff (-a) (latticeTranslate a c) v.val r).mpr v.property
          simpa [latticeTranslate_neg_cancel] using h⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact latticeTranslate_neg_cancel a v.val
      right_inv := by
        intro v
        apply Subtype.ext
        simp [latticeTranslate] }
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_translate_iff a u.val v.val

section
variable (a : LatticeVertex)
/-- Translation of a whole-lattice edge state: its value at an edge is the
old value at that edge translated back by `a`. -/
def latticeConfigurationTranslationHomeomorph  :
    LatticeConfiguration ≃ₜ LatticeConfiguration :=
  Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a))

def latticeConfigurationTranslate  : LatticeConfiguration ≃ LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph a).toEquiv

theorem latticeConfigurationTranslate_measurable  :
    Measurable (latticeConfigurationTranslate a) :=
  (latticeConfigurationTranslationHomeomorph a).continuous_toFun.measurable
end

theorem boundaryConditionIso_free_empty (e : G ≃g H) :
    boundaryConditionIso e (BoundaryCondition.free (∅ : Set V)) =
      BoundaryCondition.free (∅ : Set W) := by
  simp only [boundaryConditionIso, BoundaryCondition.free, Setoid.comap]
  aesop

@[simp] theorem latticeConfigurationTranslate_apply (a : LatticeVertex)
    (ω : LatticeConfiguration) (e : squareLattice.edgeSet) :
    latticeConfigurationTranslate a ω e =
      ω (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) e) := by
  simp [latticeConfigurationTranslate, latticeConfigurationTranslationHomeomorph,
    Homeomorph.piCongrLeft, Equiv.piCongrLeft, SimpleGraph.Iso.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet, latticeTranslationIso, latticeTranslate]

section
variable (a c : LatticeVertex) (r : ℕ)
@[simp] theorem boxVertexTranslationIso_apply (v : BoxVertex c r) :
    (boxVertexTranslationIso a c r v).val = latticeTranslate a v.val := rfl

theorem boxEdgeEmbedding_translation (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding (latticeTranslate a c) r
        (SimpleGraph.Iso.mapEdgeSet (boxVertexTranslationIso a c r) e) =
      SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a) (boxEdgeEmbedding c r e) := by
  apply Subtype.ext
  simp only [boxEdgeEmbedding, boxGraphEmbedding, SimpleGraph.Embedding.mapEdgeSet_apply,
    SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]
  rw [Sym2.map_map, Sym2.map_map]
  rfl

theorem boxEmbeddedEdgeSet_translation (A : Configuration (boxGraph c r)) :
    (configurationIso (boxVertexTranslationIso a c r) A).map
      (boxEdgeEmbedding (latticeTranslate a c) r) =
      (A.map (boxEdgeEmbedding c r)).map
        (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a)).toEmbedding := by
  change (A.map (configurationIsoEdgeEquiv (boxVertexTranslationIso a c r)).toEmbedding).map
      (boxEdgeEmbedding (latticeTranslate a c) r) =
    (A.map (boxEdgeEmbedding c r)).map
      (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a)).toEmbedding
  rw [Finset.map_map, Finset.map_map]
  have hEmb :
      (configurationIsoEdgeEquiv (boxVertexTranslationIso a c r)).toEmbedding.trans
          (boxEdgeEmbedding (latticeTranslate a c) r) =
        (boxEdgeEmbedding c r).trans
          (SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a)).toEmbedding := by
    apply Function.Embedding.ext
    intro e
    exact boxEdgeEmbedding_translation a c r e
  simp_all

theorem boxConfiguration_translation_commute (A : Configuration (boxGraph c r)) :
    boxConfiguration (latticeTranslate a c) r (configurationIso (boxVertexTranslationIso a c r) A) =
      latticeConfigurationTranslate a (boxConfiguration c r A) := by
  funext e
  simp only [boxConfiguration, latticeConfigurationTranslate_apply]
  rw [boxEmbeddedEdgeSet_translation]
  simp
  rfl
end

section
variable (q : Parameters) (a c : LatticeVertex) (r : ℕ)
/-- The finite free box PMF translates exactly to the same-radius box at the
translated center. -/
theorem boxLaw_translation_map  :
    PMF.map (latticeConfigurationTranslate a) (boxLaw q c r) =
      boxLaw q (latticeTranslate a c) r := by
  rw [boxLaw, boxLaw, PMF.map_comp]
  have hcomp :
      latticeConfigurationTranslate a ∘ boxConfiguration c r =
        boxConfiguration (latticeTranslate a c) r ∘ configurationIso (boxVertexTranslationIso a c r) := by
    grind [boxConfiguration_translation_commute]
  rw [hcomp, ← PMF.map_comp]
  rw [law_configurationIso_map q (boxVertexTranslationIso a c r)
      (BoundaryCondition.free (∅ : Set (BoxVertex c r)))]
  rw [boundaryConditionIso_free_empty]

/-- The same exact translation identity for the associated probability
measures, using the measurable product homeomorphism. -/
theorem boxProbabilityMeasure_translation_map  :
    ProbabilityMeasure.map (boxProbabilityMeasure q c r) (latticeConfigurationTranslate a) =
      boxProbabilityMeasure q (latticeTranslate a c) r := by
  apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
  change Measure.map (latticeConfigurationTranslate a) (boxLaw q c r).toMeasure =
    (boxLaw q (latticeTranslate a c) r).toMeasure
  rw [PMF.toMeasure_map _ _ (latticeConfigurationTranslate_measurable a)]
  simp [PMF.toMeasure, boxLaw_translation_map]
end

end
end PottsDiscontinuity.FK
