module

public import NearlyMinimax.SampleBlocks


@[expose] public section

/-! Exact sample-law splitting while discarding unused observations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable (d m r : ℕ)

def initialSampleSplitEquiv   :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin m ⊕ Fin r => Observation d)
    (finSumFinEquiv : (Fin m ⊕ Fin r) ≃ Fin (m + r)).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => Observation d))

def initialSampleBlock  z  :=
  (initialSampleSplitEquiv d m r z).1
end


theorem initialSampleBlock_measurePreserving {d } C
    θ (hθ : Admissible C θ) m r :
    MeasurePreserving (initialSampleBlock d m r) (sampleLaw θ (m + r)) (sampleLaw θ m) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ m
  let := sampleLaw_isProbability C θ hθ r
  have h1 := measurePreserving_piCongrLeft
    (fun _ : Fin m ⊕ Fin r => observationLaw θ)
    (finSumFinEquiv : (Fin m ⊕ Fin r) ≃ Fin (m + r)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => observationLaw θ)
  have hf : MeasurePreserving
      (Prod.fst : ((Fin m → Observation d) × (Fin r → Observation d)) → (Fin m → Observation d))
      ((sampleLaw θ m).prod (sampleLaw θ r)) (sampleLaw θ m) := measurePreserving_fst
  exact hf.comp (h2.comp h1)

def sampleBlocksWithRemainder d a b c r
    z  :=
  sampleBlockSplitEquiv d a b c (initialSampleBlock d (a + b + c) r z)

theorem sampleBlocksWithRemainder_measurePreserving {d } C
    θ (hθ : Admissible C θ) a b c r :
    MeasurePreserving (sampleBlocksWithRemainder d a b c r) (sampleLaw θ (a + b + c + r))
      (((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c)) :=
  (sampleBlockSplit_measurePreserving C θ hθ a b c).comp
    (initialSampleBlock_measurePreserving C θ hθ (a + b + c) r)

section
variable {d a b c r : ℕ}

def blockEstimatorWithRemainder 
    (T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ)
    (hmT : Measurable T) : Estimator d (a + b + c + r) :=
  ⟨fun z => T (sampleBlocksWithRemainder d a b c r z),
    hmT.comp ((sampleBlockSplitEquiv d a b c).measurable.comp
      (measurable_fst.comp (initialSampleSplitEquiv d (a + b + c) r).measurable))⟩

theorem blockEstimatorWithRemainder_risk_eq  (C : ModelConstants d)
    θ (hθ : Admissible C θ)
    T
    hmT :
    meanSquaredRisk (blockEstimatorWithRemainder (r := r) T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c) := (sampleBlocksWithRemainder_measurePreserving C θ hθ a b c r).lintegral_comp
    (((hmT.sub measurable_const).pow_const 2).ennreal_ofReal)
end


end NearlyMinimax
