module

public import proofs.HordijkSteelThreshold.RecordTargetTrial

public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold

variable {L B : ℕ}

/-- The first record above a completed prefix occurs by twice that prefix. -/
theorem generated_or_bounded_record  (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
        FiniteReversibleGenerated v.length L field v := by
  induction h with
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he <;> rcases ihv with hv | he
    · have := finiteReversibleGenerated_length_le hu
      have := finiteReversibleGenerated_length_le hv
      by_cases hlen : (u++v).length ≤ B
      · exact .inl $ .ligate hu hv ho hlen
      · exact .inr ⟨u++v, by omega, by grind, .ligate (finiteReversibleGenerated_mono_cap (by omega) hu)
          (finiteReversibleGenerated_mono_cap (by omega) hv) ho le_rfl⟩
    all_goals simp_all
  | _ => grind [FiniteReversibleGenerated]

theorem escape_has_bounded_record  (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
      FiniteReversibleGenerated v.length L field v := by
  obtain ⟨w,hw,hg⟩ := h
  have := finiteReversibleGenerated_length_le (N := B) (L := L) (field := field) (w := w)
  grind [generated_or_bounded_record hLB hg]

end RAFCriticalWindowQuantitative
