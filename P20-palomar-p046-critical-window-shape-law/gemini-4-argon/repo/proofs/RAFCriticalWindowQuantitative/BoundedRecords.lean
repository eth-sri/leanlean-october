module

public import proofs.HordijkSteelThreshold.RecordTargetTrial

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold

/-- The first record above a completed prefix occurs by twice that prefix. -/
theorem generated_or_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
        FiniteReversibleGenerated v.length L field v := by
  induction h with
  | food hn hL => exact Or.inl (.food hn hL (hL.trans hLB))
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he
    · rcases ihv with hv | he
      · by_cases hlen : (u++v).length ≤ B
        · exact Or.inl (.ligate hu hv ho hlen)
        · have huB := finiteReversibleGenerated_length_le hu
          have hvB := finiteReversibleGenerated_length_le hv
          exact Or.inr ⟨u++v, by omega, by simp only [List.length_append]; omega,
            .ligate (finiteReversibleGenerated_mono_cap (by omega) hu)
              (finiteReversibleGenerated_mono_cap (by omega) hv) ho le_rfl⟩
      · exact Or.inr he
    · exact Or.inr he
  | left hu hv _ ho ih => exact ih.imp (fun hp => .left hu hv hp ho) id
  | right hu hv _ ho ih => exact ih.imp (fun hp => .right hu hv hp ho) id

theorem escape_has_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
      FiniteReversibleGenerated v.length L field v :=
  let ⟨_, hw, hg⟩ := h
  (generated_or_bounded_record hLB hg).resolve_left fun hf => (finiteReversibleGenerated_length_le hf).not_gt hw

end RAFCriticalWindowQuantitative
