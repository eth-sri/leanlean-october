module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

variable (P : ℕ → Prop)

/-- A decreasing Boolean history is on exactly before its death index.
Death zero means initially absent; death T+1 means surviving the horizon. -/
def decreasingHistory  (T d : ℕ) : Prop :=
  ∀ t ≤ T, P t ↔ t < d

variable (T : ℕ)

theorem decreasingHistory_zero_iff
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T 0 ↔ ¬ P 0 := by grind [decreasingHistory]

theorem decreasingHistory_survives_iff
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T (T + 1) ↔ P T := by grind [decreasingHistory]

theorem decreasingHistory_dies_iff  (T d : ℕ)
    (hd : 0 < d) (hdT : d ≤ T)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T d ↔ ¬ P d ∧ P (d - 1) := by grind [decreasingHistory]

/-- Exact column weight, including initially absent and horizon-surviving
columns. Only cardinalities of deterministic nested pools enter. -/
noncomputable def columnHistoryWeight (q : ENNReal) (sizes : ℕ → ℕ) (T d : ℕ) : ENNReal :=
  if d = 0 then q ^ sizes 0
  else if T < d then 1 - q ^ sizes T
  else q ^ sizes d - q ^ sizes (d - 1)

/-- Every decreasing finite Boolean history has a bounded death index. -/
theorem exists_history_death
    (hP : ∀ a b, a ≤ b → P b → P a) :
    ∃ d ≤ T + 1, ∀ t ≤ T, P t ↔ t < d := by
  classical
  by_cases h : ∃ t, t ≤ T ∧ ¬ P t
  · refine ⟨Nat.find h, (Nat.find_spec h).1.trans $ Nat.le_succ T, ?_⟩
    aesop
  aesop

end HordijkSteelThreshold
