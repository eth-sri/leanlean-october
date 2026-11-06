module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import proofs.HordijkSteelThreshold.ReversibleRecordEvents

@[expose] public section

namespace HordijkSteelThreshold
open Classical

abbrev RecordPrefixIndex := Σ M : ℕ, (splitPrefixCoordinates M → Prop)

def recordPrefixAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | currySplitField ω ∈ firstRecordEvent 2 B i.1 ∧
    ∀ z : splitPrefixCoordinates i.1, ω z.val = i.2 z}

theorem recordPrefixAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (recordPrefixAtom B i) :=
  fun _ _ he => and_congr
    (firstRecordEvent_congr_prefix fun w hw k hk => he (w, k) ((mem_splitPrefixCoordinates _ _).mpr ⟨hw, hk⟩))
    (forall_congr' fun z => by rw [he z.val z.property])

theorem recordPrefixAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (recordPrefixAtom B i) (recordPrefixAtom B j) := by
  rw [Set.disjoint_left]; rintro ω hi hj
  by_cases hM : i.1 = j.1
  · rcases i with ⟨M, η⟩; rcases j with ⟨N, ξ⟩
    cases hM
    exact hij (congrArg (Sigma.mk M) (funext fun z => (hi.2 z).symm.trans (hj.2 z)))
  · exact Set.disjoint_left.mp (firstRecordEvent_disjoint 2 B hM) hi.1 hj.1

theorem recordPrefixAtom_word (B : ℕ) (i : RecordPrefixIndex)
    (hne : (recordPrefixAtom B i).Nonempty) :
    ∃ w : List Bool, w.length = i.1 ∧ B < w.length ∧
      ∀ ω ∈ recordPrefixAtom B i,
        FiniteReversibleGenerated w.length 2 (currySplitField ω) w := by
  obtain ⟨η, hη⟩ := hne
  obtain ⟨w, hw, hg⟩ := hη.1.2.1
  exact ⟨w, hw, hw ▸ hη.1.1, fun ω hω => hw ▸ finiteReversibleGenerated_transfer_prefix le_rfl
    (fun v hv k hk => (hη.2 ⟨(v, k), (mem_splitPrefixCoordinates _ _).mpr ⟨hv, hk⟩⟩).trans
      (hω.2 ⟨(v, k), (mem_splitPrefixCoordinates _ _).mpr ⟨hv, hk⟩⟩).symm) hg⟩

end HordijkSteelThreshold
