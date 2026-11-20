module

public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.FK.WiredBoxTranslation

/-!
# Translation invariance on the exact frozen carrier

Uniqueness of the frozen cylinder characterization transfers the invariance of
the canonical free and wired limits to every measure satisfying that
characterization at interior edge parameters.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- Fixed-center exhaustions give the same limit before and after transport. -/
private theorem boxLimit_map_eq {F : LatticeVertex → ℕ → ProbabilityMeasure LatticeConfiguration}
    {μ : ProbabilityMeasure LatticeConfiguration}
    (h : WeakBoxLimit F μ)
    (e : squareLattice ≃g squareLattice)
    (hm : ∀ c r, (F c r).map (latticeConfigurationIsoHomeomorph e) = F (e c) r) :
    μ.map (latticeConfigurationIsoHomeomorph e) = μ := by
  have hc (c : LatticeVertex) : Tendsto (fun n => F c n) atTop (𝓝 μ) := by
    refine h (fun _ => c) id (fun n => latticeBox_mono c (Nat.le_succ n)) (fun v => ?_)
    obtain ⟨n, hn⟩ := origin_latticeBox_exhaustive (latticeTranslate (-c) v)
    exact ⟨n, by simpa [latticeTranslate] using
      (mem_latticeBox_translate_iff c (0, 0) (latticeTranslate (-c) v) n).mpr hn⟩
  have ht := ((ProbabilityMeasure.continuous_map
    (latticeConfigurationIsoHomeomorph e).continuous).tendsto μ).comp (hc (0, 0))
  change Tendsto (fun n => (F (0, 0) n).map (latticeConfigurationIsoHomeomorph e)) _ _ at ht
  exact tendsto_nhds_unique (by simpa only [hm] using ht) (hc (e (0, 0)))

theorem Internal.freeBoxLimit_latticeIso_invariant (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ProbabilityMeasure.map (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (latticeConfigurationIsoHomeomorph e) = Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) :=
  boxLimit_map_eq (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1 e
    (boxProbabilityMeasure_iso_map q e hbox)

open RCInfinite

/-- Every interior-parameter frozen limit is invariant under every lattice translation. -/
theorem isRCInfiniteVolumeLimit_interior_translation_invariant
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ := by
  obtain ⟨ν, hν, _⟩ := boxMeasure_existsUnique θ i
  rw [rc_limit_eq_of_weakBoxLimit hμ hν]
  apply congrArg ProbabilityMeasure.toMeasure
    (boxLimit_map_eq hν (latticeTranslationIso a) ?_)
  intro c r
  fin_cases i
  · exact boxProbabilityMeasure_iso_map θ (latticeTranslationIso a) (mem_latticeBox_translate_iff a) c r
  · exact wiredBoxProbabilityMeasure_iso_map (latticeTranslationIso a) (mem_latticeBox_translate_iff a) c r θ

end

end PottsDiscontinuity.FK
