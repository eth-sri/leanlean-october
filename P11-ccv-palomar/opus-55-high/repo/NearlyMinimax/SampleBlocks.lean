module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Three disjoint blocks of the original sample law, with exact product law. -/
𝚯
𝚮
𝚨
𝚩

 set_option hygiene false
𝗇 𝔄 (Fin a ⊕ Fin b) ⊕ Fin c
𝗇 𝔅 𝗓₁ + c
def sampleBlockIndexEquiv (a b c : ℕ) :
    𝔄 ≃ Fin 𝔅 :=
  (Equiv.sumCongr finSumFinEquiv $ Equiv.refl $ Fin c ).trans finSumFinEquiv

𝗃 𝔇 Fin ἀ → Observation d
def sampleBlockSplitEquiv (d a b c : ℕ) :
    𝔇 𝔅 ≃ᵐ
       (𝔇 a × 𝔇 b) × 𝔇 c :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : 𝔄 => Observation d)
    (sampleBlockIndexEquiv a b c).symm).trans
  $ (MeasurableEquiv.sumPiEquivProdPi
     fun _ : 𝔄 => Observation d ).trans
  $ MeasurableEquiv.prodCongr
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin a ⊕ Fin b => Observation d )
    $ MeasurableEquiv.refl 𝔇 c

theorem sampleBlockSplit_measurePreserving C
    θ (hθ : 𝙟) a b c :
    MeasurePreserving (sampleBlockSplitEquiv d a b c) (sampleLaw θ 𝔅)
      $ ((sampleLaw θ a).prod $ sampleLaw θ b ).prod $ sampleLaw θ c := by
  let := 𝙱
  let := sampleLaw_isProbability C θ hθ c
  have h1 := measurePreserving_piCongrLeft
    (fun _ => observationLaw θ) (sampleBlockIndexEquiv a b c).symm
  have h2 := measurePreserving_sumPiEquivProdPi
     fun _ : 𝔄 => observationLaw θ
  have h3 := (measurePreserving_sumPiEquivProdPi
     fun _ : Fin a ⊕ Fin b => observationLaw θ ).prod $ MeasurePreserving.id $ sampleLaw θ c
  exact h3.comp $ h2.comp h1
