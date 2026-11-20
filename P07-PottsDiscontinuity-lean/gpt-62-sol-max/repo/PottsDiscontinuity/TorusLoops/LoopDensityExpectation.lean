module

public import PottsDiscontinuity.TorusLoops.LoopDensityObservable
public import PottsDiscontinuity.TorusLoops.LoopTailSeamBound

/-!
# Finite-volume expectation bounds from the winding-loop tail

These inequalities are the finite-sum form of the truncation step in (3.18).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC
open scoped Classical

variable {N M : ℕ}

noncomputable section

section

variable
  (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M))

private theorem torusRC_sum_scaled_indicator (c : ℝ) :
    ∑ A, torusRCMass hN hM q A * (c * (if A ∈ E then (1 : ℝ) else 0)) =
      c * phi_T_probability hN hM q E := by
  simp [phi_T_probability_eq_sum, Set.indicator, Finset.mul_sum, mul_comm]

private theorem torusRCProbability_compl :
    phi_T_probability hN hM q E + phi_T_probability hN hM q Eᶜ = 1 := by
  rw [phi_T_probability_eq_sum, phi_T_probability_eq_sum, ← Finset.sum_add_distrib]
  simpa using sum_torusRCMass hN hM q

end

section

variable
  (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ))

theorem phi_T_windingLoopDensityExpectation_pos :
    0 < phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  unfold phi_T_windingLoopDensityExpectation
  simp [torusRCMass_pos, windingLoopDensityWeight_pos, Finset.sum_pos]

/-- The weighted expectation is bounded by a low-count contribution and the
global observable bound times the large-loop tail probability. -/
theorem phi_T_windingLoopDensityExpectation_le_tail (m : ℕ) :
    phi_T_windingLoopDensityExpectation hN hM hNp hMp q ≤
      windingLoopDensityUpperBase q ^ m +
        windingLoopDensityUpperBase q ^ (N + M) *
          phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) := by
  let T := windingLoopTailEvent hN hM hNp hMp m
  let U := windingLoopDensityUpperBase q
  unfold phi_T_windingLoopDensityExpectation
  calc
    _ ≤ ∑ A, torusRCMass hN hM q A * (U ^ m + U ^ (N + M) * (if A ∈ T then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_left _ (torusRCMass_pos hN hM q A).le
      by_cases ht : A ∈ T
      · simp only [ht, ite_true, mul_one]
        exact (windingLoopDensityWeight_le_global hN hM hNp hMp q A).trans
          (le_add_of_nonneg_left (pow_nonneg (zero_le_one.trans (windingLoopDensityUpperBase_ge_one q)) _))
      · simpa [ht] using windingLoopDensityWeight_le_of_count_le hN hM hNp hMp q m A
          (le_of_lt (by simpa [T, windingLoopTailEvent] using ht))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, sum_torusRCMass, one_mul, torusRC_sum_scaled_indicator]

/-- The lower truncated-moment estimate. The tail loss is exactly the
probability of at least `m` nonzero-winding loops. -/
theorem phi_T_windingLoopDensityExpectation_ge_tail (m : ℕ) :
    windingLoopDensityLowerBase q ^ m / q.val *
        (1 - phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)) ≤
      phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  let T := windingLoopTailEvent hN hM hNp hMp m
  change _ * (1 - phi_T_probability hN hM q T) ≤ _
  rw [show 1 - phi_T_probability hN hM q T = phi_T_probability hN hM q Tᶜ by
    linarith [torusRCProbability_compl hN hM q T], ← torusRC_sum_scaled_indicator]
  apply Finset.sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_left _ (torusRCMass_pos hN hM q A).le
  by_cases ht : A ∈ T
  · simpa [ht] using (windingLoopDensityWeight_pos hN hM hNp hMp q A).le
  · simpa [ht] using windingLoopDensityWeight_ge_of_count_lt hN hM hNp hMp q m A
      (by simpa [T, windingLoopTailEvent] using ht)

end

end

end PottsDiscontinuity.TorusLoops
