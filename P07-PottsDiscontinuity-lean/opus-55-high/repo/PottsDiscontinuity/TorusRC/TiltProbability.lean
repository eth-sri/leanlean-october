module

public import PottsDiscontinuity.TorusRC.SelfDualTilt

/-! # Comparing the self-dual tilt with the standard torus law -/

@[expose] public noncomputable section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
include q
theorem tiltWeight_pos (A : RCConfig N M) :
    0 < torusRCTiltWeight hN hM q A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  exact div_pos (torusRCWeight_pos hN hM q A)
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

/-- The self-dual tilted partition function on the indexed torus. -/
def torusRCTiltPartition  : ℝ := ∑ A, torusRCTiltWeight hN hM q A

theorem torusRCTiltPartition_pos  : 0 < torusRCTiltPartition hN hM q :=
  Finset.sum_pos (fun A _ => tiltWeight_pos hN hM q A) Finset.univ_nonempty

/-- The unnormalized tilted mass of an event. -/
def torusRCTiltEventWeight (E : Set (RCConfig N M)) : ℝ :=
  ∑ A, E.indicator (torusRCTiltWeight hN hM q) A

/-- Event probability for the normalized self-dual tilted weight. -/
def torusRCTiltProbability (E : Set (RCConfig N M)) : ℝ :=
  torusRCTiltEventWeight hN hM q E / torusRCTiltPartition hN hM q

theorem torusRCWeight_eq_tilt_mul_net (A : RCConfig N M) :
    torusRCWeight hN hM q A =
      torusRCTiltWeight hN hM q A * q.val ^ rcNetIndicator hN hM A := by
  rw [torusRCTiltWeight_eq_standard_div_net]
  have hq : q.val ^ rcNetIndicator hN hM A ≠ 0 :=
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _).ne'
  simp_all

theorem netCorrection_bounds (A : RCConfig N M) :
    1 ≤ q.val ^ rcNetIndicator hN hM A ∧
      q.val ^ rcNetIndicator hN hM A ≤ q.val := by
  have hnet : rcNetIndicator hN hM A = 0 ∨ rcNetIndicator hN hM A = 1 := by
    grind [rcNetIndicator]
  aesop

theorem torusRCWeight_tilt_bounds (A : RCConfig N M) :
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

theorem torusRCTiltPartition_le_standard  :
    torusRCTiltPartition hN hM q ≤ torusRCPartition hN hM q :=
  Finset.sum_le_sum fun A _ => (torusRCWeight_tilt_bounds hN hM q A).1

theorem torusRCPartition_le_q_mul_tilt  :
    torusRCPartition hN hM q ≤ q.val * torusRCTiltPartition hN hM q := by
  unfold torusRCTiltPartition torusRCPartition FK.FiniteProbability.partition
  calc
    _ ≤ ∑ A, q.val * torusRCTiltWeight hN hM q A :=
      Finset.sum_le_sum fun A _ => (torusRCWeight_tilt_bounds hN hM q A).2
    _ = _ := by rw [Finset.mul_sum]
end

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M))
theorem torusRCTiltEventWeight_nonneg  :
    0 ≤ torusRCTiltEventWeight hN hM q E := by
  apply Finset.sum_nonneg
  grind [Set.indicator, tiltWeight_pos]

theorem torusRCTiltEventWeight_le_standard_numerator
     :
    torusRCTiltEventWeight hN hM q E ≤
      ∑ A, E.indicator (torusRCWeight hN hM q) A := by
  apply Finset.sum_le_sum
  grind [Set.indicator, torusRCWeight_tilt_bounds]

theorem torusRCEventWeight_le_q_mul_tilt_numerator
     :
    (∑ A, E.indicator (torusRCWeight hN hM q) A) ≤
      q.val * torusRCTiltEventWeight hN hM q E := by
  unfold torusRCTiltEventWeight
  calc
    _ ≤ ∑ A, q.val * E.indicator (torusRCTiltWeight hN hM q) A := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hA : A ∈ E
      · simp_all [Set.indicator, torusRCWeight_tilt_bounds]
      simp_all
    _ = _ := by rw [Finset.mul_sum]

theorem torusRCProbability_eq_standard_weight_ratio
     :
    torusRCProbability hN hM q E =
      (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q := by
  rw [torusRCProbability_eq_sum]
  calc
    _ = ∑ A, E.indicator (torusRCWeight hN hM q) A /
          torusRCPartition hN hM q := by
      grind [Set.indicator, torusRCMass]
    _ = (∑ A, E.indicator (torusRCWeight hN hM q) A) /
          torusRCPartition hN hM q := by
      rw [← Finset.sum_div]

/-- Standard and self-dual tilted event probabilities differ by at most one
factor of `q`, uniformly in the event and the torus periods. -/
theorem torusRCTiltProbability_comparison  :
    torusRCTiltProbability hN hM q E / q.val ≤
        torusRCProbability hN hM q E ∧
      torusRCProbability hN hM q E ≤
        q.val * torusRCTiltProbability hN hM q E := by
  have hstdZ := torusRCPartition_pos hN hM q
  have htiltZ := torusRCTiltPartition_pos hN hM q
  have hnumT := torusRCTiltEventWeight_nonneg hN hM q E
  have hdenSupper := torusRCPartition_le_q_mul_tilt hN hM q
  have hdenSlower := torusRCTiltPartition_le_standard hN hM q
  have hnumLower := torusRCTiltEventWeight_le_standard_numerator hN hM q E
  have hnumUpper := torusRCEventWeight_le_q_mul_tilt_numerator hN hM q E
  rw [torusRCTiltProbability, torusRCProbability_eq_standard_weight_ratio]
  constructor
  · have hratio : torusRCTiltEventWeight hN hM q E /
        (q.val * torusRCTiltPartition hN hM q) ≤
          (∑ A, E.indicator (torusRCWeight hN hM q) A) /
            torusRCPartition hN hM q := by
      apply (div_le_div_iff₀
        (mul_pos (by grind) htiltZ) hstdZ).2
      nlinarith
    simpa [div_div, mul_comm] using hratio
  · have hratio : (∑ A, E.indicator (torusRCWeight hN hM q) A) /
        torusRCPartition hN hM q ≤
          (q.val * torusRCTiltEventWeight hN hM q E) /
            torusRCTiltPartition hN hM q := by
      apply (div_le_div_iff₀ hstdZ htiltZ).2
      nlinarith
    grind
end

end PottsDiscontinuity.TorusRC
