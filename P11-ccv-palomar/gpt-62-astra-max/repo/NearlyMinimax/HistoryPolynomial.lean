module

public import Mathlib

@[expose] public section

/-!
# The actual finite heap deletion polynomial

For a finite partially ordered history, coefficients enumerate all successive
deletions of maximal pieces, with their signed mark weights. Dividing the
degree-k coefficient by k! is the combinatorial order-volume coefficient.
The derivative identity is proved from this enumeration, without assuming
a transport recurrence.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyMaximalPieces (S : Finset α) : Finset α := by
  classical
  exact S.filter (fun x => ∀ y ∈ S, x ≤ y → y = x)

theorem mem_historyMaximalPieces {S : Finset α} {x : α} :
    x ∈ historyMaximalPieces S ↔ x ∈ S ∧ ∀ y ∈ S, x ≤ y → y = x := by
  classical
  simp [historyMaximalPieces]

theorem historyMaximalPieces_subset (S : Finset α) : historyMaximalPieces S ⊆ S := fun x hx => (mem_historyMaximalPieces.1 hx).1

def historyDeletionCoefficient (weight : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, S => ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)

attribute [simp] historyDeletionCoefficient.eq_1

variable (weight : α → ℝ) (S : Finset α) (t : ℝ)

@[simp] theorem historyDeletionCoefficient_succ (k : ℕ) (S : Finset α) :
    historyDeletionCoefficient weight (k + 1) S =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x) := rfl

def historyDeletionPolynomial : ℝ :=
  ∑ k ∈ Finset.range (S.card + 1), t ^ k / k.factorial * historyDeletionCoefficient weight k S

@[simp] theorem historyDeletionPolynomial_at_zero :
    historyDeletionPolynomial weight S 0 = 1 := by
  unfold historyDeletionPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

theorem historyDeletionPolynomial_derivative_formula :
    HasDerivAt (historyDeletionPolynomial weight S)
      (∑ k ∈ Finset.range (S.card + 1),
        k * t ^ (k - 1) / k.factorial * historyDeletionCoefficient weight k S) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  simpa using (((hasDerivAt_id t).pow k).div_const k.factorial).mul_const
    (historyDeletionCoefficient weight k S)

theorem historyDeletionPolynomial_derivative_shift :
    (∑ k ∈ Finset.range (S.card + 1),
      k * t ^ (k - 1) / k.factorial * historyDeletionCoefficient weight k S) =
    ∑ k ∈ Finset.range S.card, t ^ k / k.factorial * historyDeletionCoefficient weight (k + 1) S := by
  rw [Finset.sum_range_succ']
  simp
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem historyDeletionPolynomial_derivative_deletion :
    (∑ k ∈ Finset.range S.card, t ^ k / k.factorial * historyDeletionCoefficient weight (k + 1) S) =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) t := by
  simp_rw [historyDeletionCoefficient_succ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hxS := historyMaximalPieces_subset S hx
  have hc : (S.erase x).card + 1 = S.card := by
    grind
  unfold historyDeletionPolynomial
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end NearlyMinimax
