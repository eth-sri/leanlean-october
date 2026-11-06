module

public import NearlyMinimax.HistoryMarkedAppend
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Joint measurability of the actual marked-history append operation
-/

𝚯
𝚨

𝗇 𝔇 ∀ i, MeasurableSpace $ X i
/-- The sum sigma-algebra makes sectionwise measurable maps measurable. -/
theorem historySigma_measurable_iff
    [𝔇] [MeasurableSpace Y] (f : Sigma X → Y) :
    Measurable f ↔ ∀ i, Measurable fun x => f ⟨i, x⟩ := by
  constructor
  · intro hf i
    exact hf.comp $ Measurable.of_le_map $ iInf_le _ i
  · intro hf s hs
    rw [MeasurableSpace.measurableSet_iInf]
    bound

𝗇 𝔅 Sigma fun i => X i × Y
/-- Standard Borel fibers let a product and a countable disjoint union interchange measurably. -/
def historySigmaProdMeasurableEquiv [Countable I] (X : 𝗀) (Y : Type*)
    [𝔇] [∀ i, StandardBorelSpace $ X i ]
    [MeasurableSpace Y] [StandardBorelSpace Y] : Sigma X × Y ≃ᵐ 𝔅 := by
  let := fun i => upgradeStandardBorel $ X i
  let := upgradeStandardBorel Y
  let : BorelSpace $ Sigma X := historySigma_borelSpace
  let : BorelSpace 𝔅 := historySigma_borelSpace
  exact (Homeomorph.sigmaProdDistrib (X := X) (Y := Y)).toMeasurableEquiv

𝚲

𝗇 𝔄 𝘼
𝗇 𝔈 historyCanonicalMarkAppendEquiv dependent hsymm j
/-- Apply one independent marked local update and reorder into the genuine canonical append. -/
def historyMarkedAppend (dependent : 𝙁)
    (hsymm : 𝔄)
    (j : J) [MeasurableSpace E] (h : 𝙗 × E) :
    𝙗 :=
  ⟨𝗡₁ h.1.1,
    𝔈 h.1.1 (h.2, h.1.2)⟩

/-- Both the old history and fresh mark vary measurably in the actual append operation. -/
theorem historyMarkedAppend_measurable (dependent : 𝙁)
    (hsymm : 𝔄)
    j [MeasurableSpace E] [StandardBorelSpace E] :
    Measurable $ historyMarkedAppend dependent hsymm j (E := E) := by
  let X := fun g => Fin 𝗠₁ → E
  let e := historySigmaProdMeasurableEquiv X E
  let f : Sigma (fun g => X g × E) → 𝙗 := fun h =>
    ⟨𝗡₁ h.1,
      𝔈 h.1 (h.2.2, h.2.1)⟩
  have hf : Measurable f := by
    rw [historySigma_measurable_iff]
    intro g
    exact (historyMarked_measurable_mk dependent $ 𝗡₁ g ).comp
      $ (𝔈 g).measurable.comp
        MeasurableEquiv.prodComm.measurable
  exact hf.comp e.measurable
