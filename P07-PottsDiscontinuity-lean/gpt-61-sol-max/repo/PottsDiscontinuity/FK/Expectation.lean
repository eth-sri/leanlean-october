/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Real expectations of finite probability mass functions

These are the literal finite weighted sums. The bind identity is used for
actual conditional FK mixtures, without any independence premise.
-/

@[expose] public section

namespace PottsDiscontinuity.FK.FiniteProbability

open scoped BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Real expectation on a finite sample space. -/
def expectation (p : PMF α) (f : α → ℝ)  := ∑ a, (p a).toReal * f a

section

variable (p : PMF α)
include p

theorem sum_mass_toReal  : ∑ a, (p a).toReal = 1 := by
  have hs : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [← ENNReal.toReal_sum  fun a _ => p.apply_ne_top a ,
    hs, ENNReal.toReal_one]

theorem expectation_const  (c : ℝ) : expectation p (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, sum_mass_toReal, one_mul]

theorem expectation_nonneg  (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expectation p f :=
  Finset.sum_nonneg  fun a _ => mul_nonneg ENNReal.toReal_nonneg (hf a) 

theorem expectation_mono  (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    expectation p f ≤ expectation p g :=
  Finset.sum_le_sum  fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg 

/-- Conditional expectations are averaged against the actual outer PMF. -/
theorem expectation_bind  (q : α → PMF β) (f : β → ℝ) :
    expectation (p.bind q) f = expectation p  fun a => expectation (q a) f  := by
  unfold expectation
  simp_rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum  fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top _) ,
    ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_assoc _ _ _

end

@[simp] theorem expectation_pure (a : α) (f : α → ℝ) :
    expectation (PMF.pure a) f = f a := by
  classical
  simp [expectation, apply_ite]

/-- Pushforward expectations retain the original random variable exactly. -/
theorem expectation_map (p : PMF α) (g : α → β) (f : β → ℝ) :
    expectation (p.map g) f = expectation p  fun a => f (g a)  := by
  rw [PMF.map, expectation_bind]
  simp_all

section

variable (p : PMF α) (q : α → PMF β) (f : β → ℝ) (c : ℝ)
include p q f c

/-- Any proved lower bound for every genuine conditional law bounds the mixture. -/
theorem le_expectation_bind  (h : ∀ a, c ≤ expectation (q a) f) : c ≤ expectation (p.bind q) f := by
  rw [expectation_bind, ← expectation_const p c]
  exact expectation_mono p _ _ h

/-- A proved upper bound for every genuine conditional law bounds the mixture. -/
theorem expectation_bind_le  (h : ∀ a, expectation (q a) f ≤ c) : expectation (p.bind q) f ≤ c := by
  rw [expectation_bind, ← expectation_const p c]
  exact expectation_mono p _ _ h

end

end
end PottsDiscontinuity.FK.FiniteProbability
