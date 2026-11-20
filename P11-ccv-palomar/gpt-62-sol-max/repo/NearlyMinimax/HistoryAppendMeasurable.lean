module

public import NearlyMinimax.HistoryMarkedAppend


@[expose] public section

/-!
# Joint measurability of the actual marked-history append operation
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

/-- Standard Borel fibers let a product and a countable disjoint union interchange measurably. -/
def historySigmaProdMeasurableEquiv {I : Type*} [Countable I] (X : I → Type*) (Y : Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]
    [MeasurableSpace Y] [StandardBorelSpace Y] : (Sigma X) × Y ≃ᵐ Sigma (fun i => X i × Y) := by
  let := fun i => upgradeStandardBorel (X i)
  let := upgradeStandardBorel Y
  let : BorelSpace (Sigma X) := sigma_borelSpace_actual
  let : BorelSpace (Sigma (fun i => X i × Y)) := sigma_borelSpace_actual
  exact (Homeomorph.sigmaProdDistrib (X := X) (Y := Y)).toMeasurableEquiv

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Apply one independent marked local update and reorder into the genuine canonical append. -/
def historyMarkedAppend (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] (h : HistoryMarked dependent E × E) :
    HistoryMarked dependent E :=
  ⟨historyShapeAppend dependent j h.1.1,
    historyCanonicalMarkAppendEquiv dependent hsymm j h.1.1 (h.2, h.1.2)⟩

/-- Both the old history and fresh mark vary measurably in the actual append operation. -/
theorem historyMarkedAppend_measurable (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] :
    Measurable (historyMarkedAppend dependent hsymm j (E := E)) := by
  let X := fun g : HistoryShape (fun a b => ¬ dependent a b) => Fin (historyShapeLength dependent g) → E
  let e := historySigmaProdMeasurableEquiv X E
  let f : Sigma (fun g => X g × E) → HistoryMarked dependent E := fun h =>
    ⟨historyShapeAppend dependent j h.1,
      historyCanonicalMarkAppendEquiv dependent hsymm j h.1 (h.2.2, h.2.1)⟩
  have hf : Measurable f := by
    rw [historySigma_measurable_iff]
    intro g
    exact (historyMarked_measurable_mk dependent (historyShapeAppend dependent j g)).comp
      ((historyCanonicalMarkAppendEquiv dependent hsymm j g).measurable.comp
        MeasurableEquiv.prodComm.measurable)
  exact hf.comp e.measurable

end NearlyMinimax
