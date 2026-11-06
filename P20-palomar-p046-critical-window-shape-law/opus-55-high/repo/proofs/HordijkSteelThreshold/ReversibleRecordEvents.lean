module

public import proofs.HordijkSteelThreshold.ReversibleRecordWords

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

def reversibleRecordEvent (L M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, w.length = M ∧ FiniteReversibleGenerated M L field w}

def firstRecordEvent (L B M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | B < M ∧ field ∈ reversibleRecordEvent L M ∧
    ∀ k, B < k → k < M → field ∉ reversibleRecordEvent L k}

theorem firstRecordEvent_disjoint (L B : ℕ) {M N : ℕ} (hMN : M ≠ N) :
    Disjoint (firstRecordEvent L B M) (firstRecordEvent L B N) := by
  apply Set.disjoint_left.mpr
  intro field hM hN
  rcases lt_or_gt_of_ne hMN with hlt | hgt
  · exact hN.2.2 M hM.1 hlt hM.2.1
  · exact hM.2.2 N hN.1 hgt hN.2.1

/-- Agreement on a finite rectangular prefix suffices. Including unused
split indices is harmless and leaves every later product layer unexposed. -/
theorem finiteReversibleGenerated_transfer_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k)
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L other w := by
  induction h <;> grind [FiniteReversibleGenerated, finiteReversibleGenerated_length_le]

theorem firstRecordEvent_congr_prefix {L B M : ℕ}
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ firstRecordEvent L B M ↔ other ∈ firstRecordEvent L B M := by
  have hr N hN : field ∈ reversibleRecordEvent L N ↔ other ∈ reversibleRecordEvent L N :=
    ⟨fun ⟨w,hw,hg⟩ => ⟨w,hw,finiteReversibleGenerated_transfer_prefix hN he hg⟩,
      fun ⟨w,hw,hg⟩ => ⟨w,hw,finiteReversibleGenerated_transfer_prefix hN (fun w hw k hk => (he w hw k hk).symm) hg⟩⟩
  grind [firstRecordEvent]

end HordijkSteelThreshold
