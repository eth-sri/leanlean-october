/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimit
public import PottsDiscontinuity.Duality.BoxDihedral

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

/-- A lattice graph isomorphism preserving centered box radii preserves the
unique weak limit of all nested exhaustive free-box laws. -/
theorem freeBoxLimit_latticeIso_invariant
    (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ProbabilityMeasure.map
        (Classical.choose (FK.freeBoxLimit_existsUnique q))
        (latticeConfigurationIsoHomeomorph e) =
      Classical.choose (FK.freeBoxLimit_existsUnique q) := by
  let μ :=
    Classical.choose (FK.freeBoxLimit_existsUnique q)
  let ν :=
    ProbabilityMeasure.map μ (latticeConfigurationIsoHomeomorph e)
  have hproperty :=
    (Classical.choose_spec (FK.freeBoxLimit_existsUnique q)).1
  have hboxInvCenter (c v : LatticeVertex) (r : ℕ) :
      e v ∈ latticeBox c r ↔ v ∈ latticeBox (e.symm c) r := by
    simpa using (hbox (e.symm c) v r)
  have hνproperty :
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => boxProbabilityMeasure q (c n) (r n)) atTop (𝓝 ν) := by
    intro c r hnest hexhaust
    have htransformed : ∀ n,
        latticeBox (e.symm (c n)) (r n) ⊆
          latticeBox (e.symm (c (n + 1))) (r (n + 1)) := by
      grind
    have hexhaustTransformed : ∀ v : LatticeVertex,
        ∃ n, v ∈ latticeBox (e.symm (c n)) (r n) := by
      intro v
      obtain ⟨n, hn⟩ := hexhaust (e v)
      grind
    have hmap : Tendsto
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) atTop (𝓝 ν) :=
      ((ProbabilityMeasure.continuous_map
        (latticeConfigurationIsoHomeomorph e).continuous_toFun).continuousAt.tendsto).comp (by tauto)
    have hterms :
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) =
        (fun n => boxProbabilityMeasure q (c n) (r n)) := by
      funext n
      simpa using boxProbabilityMeasure_iso_map q e hbox (e.symm (c n)) (r n)
    grind
  have huniq :=
    (Classical.choose_spec (FK.freeBoxLimit_existsUnique q)).2 ν hνproperty
  omega

end
end PottsDiscontinuity.FK.Internal
