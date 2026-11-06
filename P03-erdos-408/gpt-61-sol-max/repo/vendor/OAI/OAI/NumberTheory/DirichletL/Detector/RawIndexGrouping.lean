module

public import OAI.NumberTheory.DirichletL.Detector.MixedFubini

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve

local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal ActualEisensteinCubic.O)) := {K : Ideal ActualEisensteinCubic.O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O

def sourceRawGrouping (S : Finset (Ideal ActualEisensteinCubic.O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal ActualEisensteinCubic.O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma sourceRawGrouping_preserving  S 
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _

end SevenEighths.ProbePhysical
end

end OAI
