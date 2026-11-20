/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimitV1
public import PottsDiscontinuity.Duality.BoxDihedral

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

/-- A lattice graph isomorphism preserving centered box radii preserves the
unique weak limit of all nested exhaustive free-box laws. -/
theorem freeBoxLimit_latticeIso_invariant
    (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ProbabilityMeasure.map
        (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (latticeConfigurationIsoHomeomorph e) =
      Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) := by
  let μ :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  let ν :=
    ProbabilityMeasure.map μ (latticeConfigurationIsoHomeomorph e)
  have hproperty :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
  have hboxInvCenter (c v : LatticeVertex) (r : ℕ) :
      e v ∈ latticeBox c r ↔ v ∈ latticeBox (e.symm c) r := by
    have hh := hbox (e.symm c) v r
    simpa using hh
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
    have hμ :=
      hproperty (fun n => e.symm (c n)) r htransformed hexhaustTransformed
    have hmap : Tendsto
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) atTop (𝓝 ν) :=
      ((ProbabilityMeasure.continuous_map
        (latticeConfigurationIsoHomeomorph e).continuous_toFun).continuousAt.tendsto).comp hμ
    have hterms :
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) =
        (fun n => boxProbabilityMeasure q (c n) (r n)) := by
      funext n
      simpa using boxProbabilityMeasure_iso_map q e hbox (e.symm (c n)) (r n)
    grind
  have huniq :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).2 ν hνproperty
  assumption

end
end PottsDiscontinuity.FK.Internal
