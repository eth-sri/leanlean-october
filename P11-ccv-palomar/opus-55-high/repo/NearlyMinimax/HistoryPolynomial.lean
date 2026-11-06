module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# The actual finite heap deletion polynomial

For a finite partially ordered history, coefficients enumerate all successive
deletions of maximal pieces, with their signed mark weights. Dividing the
degree-k coefficient by k! is the combinatorial order-volume coefficient.
The derivative identity is proved from this enumeration, without assuming
a transport recurrence.
-/


𝛚

𝗇 𝔉 ∀ y ∈ S, 𝗪₂ → y = x
def historyMaximalPieces (S : Finset α) : Finset α := by
  classical
  exact S.filter fun x => 𝔉

theorem mem_historyMaximalPieces {S } {x : α} :
    x ∈ historyMaximalPieces S ↔ x ∈ S ∧ 𝔉 := by
  classical
  simp only [historyMaximalPieces, Finset.mem_filter]

theorem historyMaximalPieces_subset (S : Finset α) : historyMaximalPieces S ⊆ S := by
  intro x hx
  exact (mem_historyMaximalPieces.1 hx).1

𝗇 𝔈 ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)
𝗇 𝔍 𝘆
def historyDeletionCoefficient (weight : 𝘬) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | 𝔍, S => 𝔈

@[simp] theorem historyDeletionCoefficient_zero weight (S : Finset α) :
    historyDeletionCoefficient weight 0 S = 1 := rfl

@[simp] theorem historyDeletionCoefficient_succ weight k (S : Finset α) :
    historyDeletionCoefficient weight 𝔍 S =
      𝔈 := rfl

𝗇 𝔎 historyDeletionCoefficient weight k S
𝗇 𝔏 S.card + 1
def historyDeletionPolynomial (weight : 𝘬) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 𝔏, t ^ k / 𝖽₁ * 𝔎

𝗇 𝔊 historyDeletionPolynomial weight S
@[simp] theorem historyDeletionPolynomial_at_zero weight (S : Finset α) :
    𝔊 0 = 1 := by
  unfold historyDeletionPolynomial
  rw [Finset.sum_eq_single 0]
  all_goals simp_all

𝗇 𝔄 ∑ k ∈ Finset.range 𝔏, k * t ^ 𝗩₂ / k.factorial * 𝔎
theorem historyDeletionPolynomial_derivative_formula weight (S : Finset α) t :
    HasDerivAt 𝔊
      𝔄 t := by
  apply HasDerivAt.fun_sum
  intro k hk
  simpa only [id_eq, mul_one] using! (((hasDerivAt_id t).pow k).div_const k.factorial).mul_const
    𝔎

𝗇 𝔅 ∑ k ∈ Finset.range S.card, t ^ k / k.factorial * historyDeletionCoefficient weight 𝔍 S
theorem historyDeletionPolynomial_derivative_shift weight (S : Finset α) t :
    𝔄 =
    𝔅 := by
  rw [Finset.sum_range_succ']
  simp
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ]
  push_cast
  field_simp

𝗇 𝔇 ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) t
theorem historyDeletionPolynomial_derivative_deletion weight (S : Finset α) t :
    𝔅 =
      𝔇 := by
  simp_rw [historyDeletionCoefficient_succ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hxS := historyMaximalPieces_subset S hx
  have hc : (S.erase x).card + 1 = S.card := by
    grind
  unfold historyDeletionPolynomial
  rw [hc, Finset.mul_sum]
  grind

/-- The genuine finite deletion polynomial satisfies the exact source derivative identity. -/
theorem historyDeletionPolynomial_hasDerivAt weight (S : Finset α) t :
    HasDerivAt 𝔊
      𝔇 t := by
  have hh := historyDeletionPolynomial_derivative_formula weight S t
  rw [historyDeletionPolynomial_derivative_shift, historyDeletionPolynomial_derivative_deletion] at hh
  exact hh
