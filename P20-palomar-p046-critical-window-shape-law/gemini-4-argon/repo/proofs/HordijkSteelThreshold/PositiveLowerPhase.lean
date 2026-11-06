module

public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.CanonicalCatalysisLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete

theorem canonical_raf_measure_eq_ambient (n : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} := by
  rw [← ambientPartition_map n lambda, Measure.map_apply (measurable_of_finite _) (measurableSet_hasRAFEvent n)]
  simp only [Set.preimage, HasRAFEvent, Set.mem_ofPred_eq,
    show ∀ ω : AmbientCoord n → Prop, catalysisOf (ambientPartition ω) = fun x r => ω (x, r) from
      fun ω => funext₂ fun x r => propext (catalysisOf_ambientPartition ω x r)]

end HordijkSteelThreshold
