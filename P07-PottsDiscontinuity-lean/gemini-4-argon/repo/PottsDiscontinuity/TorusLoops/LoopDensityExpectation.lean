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

private theorem torusRC_sum_mass_indicator
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) [DecidablePred (· ∈ E)] :
    ∑ A, torusRCMass hN hM q A * (if A ∈ E then (1 : ℝ) else 0) =
      phi_T_probability hN hM q E := by
  rw [phi_T_probability_eq_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ∈ E <;> simp [Set.indicator, h]

private theorem torusRCProbability_compl
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E + phi_T_probability hN hM q Eᶜ = 1 := by
  rw [phi_T_probability_eq_sum, phi_T_probability_eq_sum, ← Finset.sum_add_distrib,
    ← sum_torusRCMass hN hM q]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ∈ E <;> simp [Set.indicator, h]

theorem phi_T_windingLoopDensityExpectation_pos
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) :
    0 < phi_T_windingLoopDensityExpectation hN hM hNp hMp q :=
  Finset.sum_pos (fun A _ => mul_pos (torusRCMass_pos hN hM q A)
    (windingLoopDensityWeight_pos hN hM hNp hMp q A)) ⟨fun _ => false, Finset.mem_univ _⟩

/-- The weighted expectation is bounded by a low-count contribution and the
global observable bound times the large-loop tail probability. -/
theorem phi_T_windingLoopDensityExpectation_le_tail
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    phi_T_windingLoopDensityExpectation hN hM hNp hMp q ≤
      windingLoopDensityUpperBase q ^ m +
        windingLoopDensityUpperBase q ^ (N + M) *
          phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) := by
  let T := windingLoopTailEvent hN hM hNp hMp m
  have hsum : phi_T_windingLoopDensityExpectation hN hM hNp hMp q ≤
      ∑ A, torusRCMass hN hM q A *
        (windingLoopDensityUpperBase q ^ m +
          windingLoopDensityUpperBase q ^ (N + M) * (if A ∈ T then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left ?_ (torusRCMass_pos hN hM q A).le
    by_cases ht : A ∈ T
    · simpa [ht] using (windingLoopDensityWeight_le_global hN hM hNp hMp q A).trans
        (le_add_of_nonneg_left (pow_nonneg (le_trans zero_le_one (windingLoopDensityUpperBase_ge_one q)) _))
    · have hc : windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A < m := by
        simpa [T, windingLoopTailEvent] using ht
      simpa [ht] using windingLoopDensityWeight_le_of_count_le hN hM hNp hMp q m A hc.le
  refine hsum.trans_eq ?_
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_torusRCMass hN hM q, one_mul,
    mul_left_comm _ (windingLoopDensityUpperBase q ^ (N + M)), ← Finset.mul_sum,
    torusRC_sum_mass_indicator]
  rfl

/-- The lower truncated-moment estimate. The tail loss is exactly the
probability of at least `m` nonzero-winding loops. -/
theorem phi_T_windingLoopDensityExpectation_ge_tail
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    windingLoopDensityLowerBase q ^ m / q.val *
        (1 - phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)) ≤
      phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  let T := windingLoopTailEvent hN hM hNp hMp m
  have hprob := torusRCProbability_compl hN hM q T
  have hsum : (∑ A, torusRCMass hN hM q A *
      (windingLoopDensityLowerBase q ^ m / q.val * (if A ∈ Tᶜ then (1 : ℝ) else 0))) ≤
      phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
    refine Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left ?_ (torusRCMass_pos hN hM q A).le
    by_cases hl : A ∈ Tᶜ
    · have hc : windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A < m := by
        simpa [T, windingLoopTailEvent] using hl
      simpa [hl] using windingLoopDensityWeight_ge_of_count_lt hN hM hNp hMp q m A hc
    · simpa [hl] using (windingLoopDensityWeight_pos hN hM hNp hMp q A).le
  simp_rw [mul_left_comm _ (windingLoopDensityLowerBase q ^ m / q.val)] at hsum
  rw [← Finset.mul_sum, torusRC_sum_mass_indicator,
    show phi_T_probability hN hM q Tᶜ = 1 - phi_T_probability hN hM q T by linarith] at hsum
  exact hsum

end

end PottsDiscontinuity.TorusLoops
