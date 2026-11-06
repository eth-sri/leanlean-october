
import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.HordijkSteelThreshold.SplitPrefixIndependence
import proofs.HordijkSteelThreshold.ReversibleRecordWords




namespace HordijkSteelThreshold


def reversibleRecordEvent (L M : ℕ)  :=
  {field | ∃ w, w.length = M ∧ FiniteReversibleGenerated M L field w}

def firstRecordEvent (L B M : ℕ)  :=
  {field | B < M ∧ field ∈ reversibleRecordEvent L M ∧
    ∀ k, B < k → k < M → field ∉ reversibleRecordEvent L k}



/-- Agreement on a finite rectangular prefix suffices. Including unused
split indices is harmless and leaves every later product layer unexposed. -/
theorem finiteReversibleGenerated_congr_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ z ∈ splitPrefixCoordinates M, field z.1 z.2 = other z.1 z.2)
    {w : List Bool} :
    FiniteReversibleGenerated N L field w ↔ FiniteReversibleGenerated N L other w := by
  simp only [Prod.forall, mem_splitPrefixCoordinates, and_imp] at he
  constructor <;> intro h <;> induction h <;> grind [FiniteReversibleGenerated, finiteReversibleGenerated_length_le]



abbrev RecordPrefixIndex := Σ M : ℕ, splitPrefixCoordinates M → Prop

variable (B : ℕ) (i : RecordPrefixIndex)

def recordPrefixAtom   :=
  {ω | currySplitField ω ∈ firstRecordEvent 2 B i.1 ∧
    ∀ z : splitPrefixCoordinates i.1, ω z.val = i.2 z}

theorem recordPrefixAtom_determined  :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (recordPrefixAtom B i) := by
  intro ω η he
  
  
  apply and_congr
  · have hr (N : ℕ) (hN : N ≤ i.1) :
        currySplitField ω ∈ reversibleRecordEvent 2 N ↔ currySplitField η ∈ reversibleRecordEvent 2 N := by
      apply exists_congr
      intro w
      exact and_congr Iff.rfl (finiteReversibleGenerated_congr_prefix hN he)
    grind [firstRecordEvent]
  · apply forall_congr'
    intro z
    rw [he z.val z.property]

theorem recordPrefixAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (recordPrefixAtom B i) (recordPrefixAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  by_cases hM : i.1 = j.1
  · 
    exact hij (by
                cases i
                cases j
                cases hM
                congr
                grind [cases Bool, recordPrefixAtom])
  · grind [recordPrefixAtom, firstRecordEvent]


theorem measurableSet_of_splitPrefixDetermined (P : _)
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  measurability

end HordijkSteelThreshold
