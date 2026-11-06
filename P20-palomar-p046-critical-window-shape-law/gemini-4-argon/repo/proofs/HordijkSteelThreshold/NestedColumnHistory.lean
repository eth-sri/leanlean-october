module

public import proofs.HordijkSteelThreshold.CohortConnectorProbability

@[expose] public section

namespace HordijkSteelThreshold

def decreasingHistory (P : ℕ → Prop) (T d : ℕ) : Prop :=
  ∀ t ≤ T, P t ↔ t < d

theorem decreasingHistory_zero_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T 0 ↔ ¬ P 0 :=
  ⟨fun h hp => by have := (h 0 (Nat.zero_le T)).mp hp; omega,
   fun h t _ => ⟨fun hp => (h (hP 0 t (Nat.zero_le t) hp)).elim, by omega⟩⟩

theorem decreasingHistory_survives_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T (T + 1) ↔ P T :=
  ⟨fun h => (h T le_rfl).mpr (Nat.lt_succ_self T),
   fun h t ht => ⟨fun _ => by omega, fun _ => hP t T ht h⟩⟩

theorem decreasingHistory_dies_iff (P : ℕ → Prop) (T d : ℕ)
    (hd : 0 < d) (hdT : d ≤ T) (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T d ↔ ¬ P d ∧ P (d - 1) :=
  ⟨fun h => ⟨fun hp => Nat.lt_irrefl d ((h d hdT).mp hp), (h (d - 1) (by omega)).mpr (by omega)⟩,
   fun ⟨hoff, hon⟩ t _ => ⟨fun hp => by by_contra h; exact hoff (hP d t (by omega) hp),
     fun _ => hP t (d - 1) (by omega) hon⟩⟩

end HordijkSteelThreshold
