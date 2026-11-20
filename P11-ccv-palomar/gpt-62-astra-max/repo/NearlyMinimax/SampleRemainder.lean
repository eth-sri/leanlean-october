module

public import NearlyMinimax.SampleBlocks


@[expose] public section

/-! Exact sample-law splitting while discarding unused observations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def initialSampleSplitEquiv (d m r : ℕ) :
    (Fin (m + r) → Observation d) ≃ᵐ ((Fin m → Observation d) × (Fin r → Observation d)) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Observation d)
    finSumFinEquiv.symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ => Observation d))

def initialSampleBlock (d m r : ℕ) (z : Fin (m + r) → Observation d) : Fin m → Observation d :=
  (initialSampleSplitEquiv d m r z).1

variable {d a b c r : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ)
    {T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ}
    (hmT : Measurable T)

include hθ in
theorem initialSampleBlock_measurePreserving (m r : ℕ) :
    MeasurePreserving (initialSampleBlock d m r) (sampleLaw θ (m + r)) (sampleLaw θ m) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ r
  have h1 := measurePreserving_piCongrLeft
    (fun _ : Fin m ⊕ Fin r => observationLaw θ)
    finSumFinEquiv.symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => observationLaw θ)
  have hf : MeasurePreserving
      Prod.fst
      ((sampleLaw θ m).prod (sampleLaw θ r)) (sampleLaw θ m) := measurePreserving_fst
  exact hf.comp (h2.comp h1)

def sampleBlocksWithRemainder (d a b c r : ℕ)
    (z : Fin (a + b + c + r) → Observation d) :
      ((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d) :=
  sampleBlockSplitEquiv d a b c (initialSampleBlock d (a + b + c) r z)

include hθ in
theorem sampleBlocksWithRemainder_measurePreserving (a b c r : ℕ) :
    MeasurePreserving (sampleBlocksWithRemainder d a b c r) (sampleLaw θ (a + b + c + r))
      (((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c)) :=
  (sampleBlockSplit_measurePreserving hθ a b c).comp
    (initialSampleBlock_measurePreserving hθ ..)

def blockEstimatorWithRemainder : Estimator d (a + b + c + r) :=
  ⟨fun z => T (sampleBlocksWithRemainder d a b c r z),
    hmT.comp ((sampleBlockSplitEquiv d a b c).measurable.comp
      (measurable_fst.comp (initialSampleSplitEquiv d (a + b + c) r).measurable))⟩

end NearlyMinimax
