
import Mathlib.Tactic




namespace HordijkSteelThreshold

variable (P : ℕ → Prop)

theorem bounded_progress  (r : ℕ → ℕ) (B : ℕ)
    (persist : ∀ n, P n → P (n+1))
    (progress : ∀ n, ¬ P n → r n < r (n+1))
    (bound : ∀ n, r n ≤ B) : P B := by
  have h : ∀ n, n ≤ r n ∨ P n := by
    intro n
    induction n <;> grind
  grind

variable {X R : Type*} [Fintype X]

/-- Active reaction history for a deterministic pool-response map. -/
def peelingActiveAt 
    (response : Finset X → Finset R) (closure : Finset R → Finset X) 
  | 0 => response Finset.univ
  | t + 1 => response (closure (peelingActiveAt response closure t))

/-- Pools computed from a prescribed active-set history, before testing it
against a random field. These are deterministic when the history is fixed. -/
def prescribedPoolAt 
    (closure : Finset R → Finset X) (history : ℕ → Finset R) 
  | 0 => Finset.univ
  | t + 1 => closure (history t)

/-- A history event is exactly the intersection of its fixed-pool response
constraints. There is no extra random closure-consistency condition. -/
theorem peeling_history_iff 
    (response : _) (closure : Finset R → Finset X)
    (history : _) (T : ℕ) :
    (∀ t ≤ T, peelingActiveAt response closure t = history t) ↔
      ∀ t ≤ T, response (prescribedPoolAt closure history t) = history t := by
  constructor <;> intro h t <;> induction t <;> grind [peelingActiveAt, prescribedPoolAt]

theorem peelingActiveAt_antitone 
    (response : _) (closure : Finset R → Finset X)
    (hresponse : Monotone response) (hclosure : Monotone closure) :
    Antitone (peelingActiveAt response closure) := by
  apply antitone_nat_of_succ_le
  intro t
  induction t <;> grind [peelingActiveAt, Monotone]




end HordijkSteelThreshold
