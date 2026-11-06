
import proofs.HordijkSteelThreshold.SourceTerminalRAF
import proofs.HordijkSteelThreshold.AmbientIndependence




namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete

variable {n : ℕ}

def ambientPartition  (ω : AmbientCoord n → Prop) : CatalysisSample n :=
  ({z | ω (z.1,z.2.val)}, {z | ω (z.1,z.2.val)})

variable (n : ℕ) (lambda : ℝ)

/-- The unpartitioned iid presentation is exactly the canonical seed/nonseed
sample measure. It has the same catalysis parameter and literal reaction IDs. -/
theorem ambientPartition_map  :
    (ambientPiMeasure n lambda).map ambientPartition = uniformCatalysisMeasure n lambda := by
  let e : SeedCoord n ⊕ NonseedCoord n ≃ AmbientCoord n :=
    (Equiv.prodSumDistrib _ _ _).symm.trans
      (Equiv.prodCongr (Equiv.refl (Molecule n)) (Equiv.sumCompl (RevSeedReaction (binaryPolymerCRS n 2))))
  let law := fun _ : SeedCoord n ⊕ NonseedCoord n => ambientCoordLaw (catalysisP n lambda)
  have h := ((measurePreserving_sumPiEquivProdPi law).comp
    (measurePreserving_piCongrLeft law e.symm)).map_eq
  simp only [MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.piCongrLeft, Equiv.piCongrLeft', Equiv.symm_symm, eq_rec_constant] at h
  
  simp only [uniformCatalysisMeasure, setBernoulli_eq_map]
  
  erw [Measure.map_id', Measure.map_id']
  simpa only [ambientPiMeasure, Measure.infinitePi_eq_pi] using! h

@[simp] theorem catalysisOf_ambientPartition  (ω : _)
    (x : Molecule n) (r : Reaction n) : catalysisOf (ambientPartition ω) x r ↔ ω (x,r) := by simp_all [catalysisOf, ambientPartition]


theorem canonical_raf_measure_eq_ambient (n : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      ambientPiMeasure n lambda {ω | ∃ S : _,
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} := by
  rw [← ambientPartition_map n lambda, Measure.map_apply (measurable_of_finite _)
    (Set.toFinite (HasRAFEvent n)).measurableSet]
  have hc (ω : AmbientCoord n → Prop) : catalysisOf (ambientPartition ω) =
      fun x r => ω (x,r) := by
    funext x r
    bound
  simp [HasRAFEvent, hc]

end HordijkSteelThreshold
