module
public import Mathlib

public import PottsDiscontinuity.TorusRC.SelfDualTilt

/-! # Comparing the self-dual tilt with the standard torus law -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

private theorem tiltWeight_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    0 < torusRCTiltWeight hN hM q A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  exact div_pos (torusRCWeight_pos hN hM q A)
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

/-- The self-dual tilted partition function on the indexed torus. -/
noncomputable def torusRCTiltPartition (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : ℝ := ∑ A, torusRCTiltWeight hN hM q A

theorem torusRCTiltPartition_pos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : 0 < torusRCTiltPartition hN hM q := sum_pos (fun A x => tiltWeight_pos hN hM q A) univ_nonempty

/-- The unnormalized tilted mass of an event. -/
noncomputable def torusRCTiltEventWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  ∑ A, E.indicator (torusRCTiltWeight hN hM q) A

/-- Event probability for the normalized self-dual tilted weight. -/
noncomputable def torusRCTiltProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M))  :=
  torusRCTiltEventWeight hN hM q E / torusRCTiltPartition hN hM q

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
include hN hM q

section

variable (A : RCConfig N M)


private theorem torusRCWeight_eq_tilt_mul_net   :
    torusRCWeight hN hM q A =
      torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  
  field_simp [ (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _).ne' ]

private theorem netCorrection_bounds   :
    1 ≤ q.val ^ rcNetIndicator hN hM A ∧
      q.val ^ rcNetIndicator hN hM A ≤ q.val := by
  
  have hnet : rcNetIndicator hN hM A = 0 ∨ rcNetIndicator hN hM A = 1 := by
    unfold rcNetIndicator
    split <;> simp
  aesop

private theorem torusRCWeight_tilt_bounds   :
    torusRCTiltWeight hN hM q A ≤ torusRCWeight hN hM q A ∧
      torusRCWeight hN hM q A ≤ q.val * torusRCTiltWeight hN hM q A := by
  rw [torusRCWeight_eq_tilt_mul_net]
  have h := netCorrection_bounds hN hM q A
  refine ⟨?_, ?_⟩
  · calc
      torusRCTiltWeight hN hM q A = torusRCTiltWeight hN hM q A * 1 := by ring
      _ ≤ torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A :=
        mul_le_mul_of_nonneg_left h.1 (tiltWeight_pos hN hM q A).le
  · calc
      torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A ≤
          torusRCTiltWeight hN hM q A * q.val :=
        mul_le_mul_of_nonneg_left h.2 (tiltWeight_pos hN hM q A).le
      _ = q.val * torusRCTiltWeight hN hM q A := by ring

end

theorem torusRCTiltPartition_le_standard  :
    torusRCTiltPartition hN hM q ≤ torusRCPartition hN hM q := sum_le_sum fun A x => (torusRCWeight_tilt_bounds hN hM q A).left

theorem torusRCPartition_le_q_mul_tilt  :
    torusRCPartition hN hM q ≤ q.val * torusRCTiltPartition hN hM q := by
  unfold torusRCTiltPartition torusRCPartition FK.FiniteProbability.partition
  calc
    _ ≤ ∑ A, q.val * torusRCTiltWeight hN hM q A :=
      Finset.sum_le_sum fun A _ => (torusRCWeight_tilt_bounds hN hM q A).2
    _ = _ := by rw [Finset.mul_sum]

section

variable (E : Set (RCConfig N M))


private theorem torusRCTiltEventWeight_nonneg   :
    0 ≤ torusRCTiltEventWeight hN hM q E := by
  
  apply Finset.sum_nonneg
  intro A _
  by_cases hA : A ∈ E
  · simp [hA]
    exact (tiltWeight_pos hN hM q A).le
  · simp [hA]

private theorem torusRCTiltEventWeight_le_standard_numerator
    
     :
    torusRCTiltEventWeight hN hM q E ≤
      ∑ A, E.indicator (torusRCWeight hN hM q) A := by
  
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A ∈ E
  · simp_all [torusRCWeight_tilt_bounds]
  · simp [hA]

private theorem torusRCEventWeight_le_q_mul_tilt_numerator
    
     :
     ∑ A, E.indicator (torusRCWeight hN hM q) A  ≤
      q.val * torusRCTiltEventWeight hN hM q E := by
  unfold torusRCTiltEventWeight
  calc
    _ ≤ ∑ A, q.val * E.indicator (torusRCTiltWeight hN hM q) A := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hA : A ∈ E
      · simp_all [torusRCWeight_tilt_bounds]
      · simp [hA]
    _ = _ := by rw [Finset.mul_sum]

private theorem torusRCProbability_eq_standard_weight_ratio
    
     :
    torusRCProbability hN hM q E =
      (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q := by
  rw [torusRCProbability_eq_sum]
  calc
    _ = ∑ A, E.indicator (torusRCWeight hN hM q) A /
          torusRCPartition hN hM q := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A ∈ E
      all_goals aesop
    _ = (∑ A, E.indicator (torusRCWeight hN hM q) A) /
          torusRCPartition hN hM q := by
      rw [← Finset.sum_div]

/-- Standard and self-dual tilted event probabilities differ by at most one
factor of `q`, uniformly in the event and the torus periods. -/
theorem torusRCTiltProbability_comparison   :
    torusRCTiltProbability hN hM q E / q.val ≤
        torusRCProbability hN hM q E ∧
      torusRCProbability hN hM q E ≤
        q.val * torusRCTiltProbability hN hM q E := by
  have hstdZ := torusRCPartition_pos hN hM q
  have htiltZ := torusRCTiltPartition_pos hN hM q
  have hnumT := torusRCTiltEventWeight_nonneg hN hM q E
  
  
  
  
  have hqpos  := lt_of_lt_of_le zero_lt_one q.property
  rw [torusRCTiltProbability, torusRCProbability_eq_standard_weight_ratio]
  constructor
  · 
    simpa [div_div, mul_comm] using  (div_le_div_iff₀ (mul_pos hqpos htiltZ) hstdZ).mpr
                                                                           (Trans.trans (mul_le_mul_of_nonneg_left (torusRCPartition_le_q_mul_tilt hN hM q) hnumT)
                                                                             (mul_le_mul_of_nonneg_right (torusRCTiltEventWeight_le_standard_numerator hN hM q E) (mul_nonneg (LT.lt.le hqpos) (LT.lt.le htiltZ)))) 
  · 
    simpa [mul_div_assoc] using  (div_le_div_iff₀ hstdZ htiltZ).mpr
                                                                           (Trans.trans (mul_le_mul_of_nonneg_right (torusRCEventWeight_le_q_mul_tilt_numerator hN hM q E) (LT.lt.le htiltZ))
                                                                             (mul_le_mul_of_nonneg_left (torusRCTiltPartition_le_standard hN hM q) (mul_nonneg (LT.lt.le hqpos) hnumT))) 

end

end

end PottsDiscontinuity.TorusRC
