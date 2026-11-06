/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

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
  let μ  :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  let ν  :=
    ProbabilityMeasure.map μ (latticeConfigurationIsoHomeomorph e)
  
  have hboxInvCenter (c v : LatticeVertex) (r : ℕ) :
      e v ∈ latticeBox c r ↔ v ∈ latticeBox (e.symm c) r := by
    
    simpa using  hbox (e.symm c) v r 
  
  
  simpa [μ, ν] using ((Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).2 ν (by
                                                                                                                                                                                       exact fun c r hnest hexhaust =>
                                                                                                                                                                                               Eq.mp
                                                                                                                                                                                                 (congrArg (fun _a => Tendsto _a atTop (𝓝 ν))
                                                                                                                                                                                                   (funext fun n =>
                                                                                                                                                                                                     Eq.mp
                                                                                                                                                                                                       (congrArg (Eq ((boxProbabilityMeasure q (e.symm (c n)) (r n)).map ⇑(latticeConfigurationIsoHomeomorph e)))
                                                                                                                                                                                                         (congrFun' (congrArg (boxProbabilityMeasure q) (RelIso.apply_symm_apply e (c n))) (r n)))
                                                                                                                                                                                                       (boxProbabilityMeasure_iso_map q e hbox (e.symm (c n)) (r n))))
                                                                                                                                                                                                 (Tendsto.comp
                                                                                                                                                                                                   (ContinuousAt.tendsto
                                                                                                                                                                                                     (Continuous.continuousAt
                                                                                                                                                                                                       (ProbabilityMeasure.continuous_map (latticeConfigurationIsoHomeomorph e).continuous_toFun)))
                                                                                                                                                                                                   (((Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1) (fun n => e.symm (c n)) r
                                                                                                                                                                                                     (fun n ⦃v⦄ hv => (hboxInvCenter (c (n + 1)) v (r (n + 1))).mp (hnest n ((hboxInvCenter (c n) v (r n)).mpr hv)))
                                                                                                                                                                                                     fun v => Exists.casesOn (hexhaust (e v)) fun n hn => Exists.intro n ((hboxInvCenter (c n) v (r n)).mp hn)))))

end
end PottsDiscontinuity.FK.Internal
