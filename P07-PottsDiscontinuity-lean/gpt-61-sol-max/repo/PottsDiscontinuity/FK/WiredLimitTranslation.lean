/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Applied to the proved common wired-box limit and wired finite translation identity. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.WiredBoxLimits
public import PottsDiscontinuity.FK.WiredBoxTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- The unique source-defined wired-box weak limit is invariant under every
integer translation of the original lattice configuration. -/
theorem wiredBoxLimit_translation_invariant (q : Parameters) (a : LatticeVertex) :
    ProbabilityMeasure.map
        (Classical.choose (PottsDiscontinuity.FK.wiredBoxLimit_existsUnique q))
        (latticeConfigurationTranslate a) =
      Classical.choose (PottsDiscontinuity.FK.wiredBoxLimit_existsUnique q) := by
  let μ  :=
    Classical.choose (PottsDiscontinuity.FK.wiredBoxLimit_existsUnique q)
  have hproperty := (Classical.choose_spec (PottsDiscontinuity.FK.wiredBoxLimit_existsUnique q)).1
  
  
  have hmap : Tendsto
      (fun n => ProbabilityMeasure.map (wiredBoxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) atTop
      (𝓝 (ProbabilityMeasure.map μ (latticeConfigurationTranslate a))) :=
    ((ProbabilityMeasure.continuous_map
      (latticeConfigurationTranslationHomeomorph a).continuous_toFun).continuousAt.tendsto).comp
      (hproperty (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive)
  have hterms :
      (fun n => ProbabilityMeasure.map (wiredBoxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) =
       (wiredBoxProbabilityMeasure q a)  := by
    funext n
    simpa [latticeTranslate] using wiredBoxProbabilityMeasure_translation_map q a (0, 0) n
  rw [hterms] at hmap
  have hEq := tendsto_nhds_unique hmap (by
                                          apply hproperty (fun _ => a)  fun n => n 
                                          · intro n
                                            exact latticeBox_mono a (Nat.le_succ n)
                                          · intro v
                                            obtain ⟨n, hn⟩ := origin_latticeBox_exhaustive (latticeTranslate (-a) v)
                                            refine ⟨n, ?_⟩
                                            simpa [latticeTranslate] using
                                              (mem_latticeBox_translate_iff a (0, 0) (latticeTranslate (-a) v) n).mpr hn)
  simpa [μ] using hEq

end
end PottsDiscontinuity.FK
