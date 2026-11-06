module

public import proofs.HordijkSteelThreshold.HistoryProductLaw
public import proofs.HordijkSteelThreshold.PeelingHistory

@[expose] public section

namespace HordijkSteelThreshold

theorem exists_history_death (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    ∃ d ≤ T + 1, ∀ t ≤ T, P t ↔ t < d := by
  classical
  by_cases h : ∃ t, t ≤ T ∧ ¬ P t
  · refine ⟨Nat.find h, (Nat.find_spec h).1.trans (Nat.le_succ T), fun t ht =>
      ⟨fun hp => by by_contra hn; exact (Nat.find_spec h).2 (hP _ t (by omega) hp),
       fun ht' => by by_contra hn; exact Nat.find_min h ht' ⟨ht, hn⟩⟩⟩
  · exact ⟨T + 1, le_rfl, fun t ht => ⟨fun _ => by omega, fun _ => by by_contra hn; exact h ⟨t, ht, hn⟩⟩⟩

end HordijkSteelThreshold
