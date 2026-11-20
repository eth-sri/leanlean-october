module

public import proofs.RAFReactionQuotient.InfiniteSource
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.SplitCylinderNull

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold
open scoped ENNReal

def quotientRecordAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | (fun z => ω (canonicalIndex z)) ∈ recordPrefixAtom B i}

theorem quotientRecordAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (quotientRecordAtom B i) := by
  intro ω η he
  apply recordPrefixAtom_determined B i
  intro z hz
  exact he (canonicalIndex z) (canonicalIndex_prefix hz)

theorem quotientRecordAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (quotientRecordAtom B i) (quotientRecordAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact Set.disjoint_left.mp (recordPrefixAtoms_disjoint B hij) hi hj

end RAFReactionQuotient
