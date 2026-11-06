module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Geometric sums in an integer gap

Companion paper, equation `eq:EmptySetCalc`. Integer endpoints can be negative.
The only spectral restriction in this finite calculation is `z(p) ≠ 1`.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable (p : ℝ)
/-- The exponential at one integer coordinate. -/
noncomputable def positionPhase (u : ℤ) : ℂ := Complex.exp (I * (p : ℂ) * (u : ℂ))

theorem positionPhase_add (a b : ℤ) :
    positionPhase p (a + b) = positionPhase p a * positionPhase p b := by
  unfold positionPhase
  rw [← Complex.exp_add]
  congr 1
  grind

@[simp] theorem positionPhase_one  : positionPhase p 1 = z p := by
  simp only [positionPhase, Int.cast_one, mul_one, z]

theorem positionPhase_nat (d : ℕ) : positionPhase p d = z p ^ d := by
  rw [positionPhase, z, ← Complex.exp_nat_mul]
  push_cast
  ring

/-- An open integer interval is a shifted natural geometric sum. -/
theorem sum_positionPhase_Ioo (a : ℤ) (d : ℕ) :
    (∑ u ∈ Ioo a (a + (d : ℤ) + 1), positionPhase p u) =
      positionPhase p (a + 1) * ∑ j ∈ range d, z p ^ j := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => a + (j : ℤ) + 1)
  · simp
  · omega
  · intro u hu
    obtain ⟨hl, hr⟩ := mem_Ioo.mp hu
    refine ⟨(u - a - 1).toNat, ?_, ?_⟩
    · grind
    omega
  grind [positionPhase_add, positionPhase_nat]
end

section
variable (c p : ℝ) {a b : ℤ} (hab : a < b)
include hab
/-- Separate the two endpoints from the interior weighted sum. -/
theorem sum_gap_endpoint_weights  :
    (∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      positionPhase p a + (c : ℂ) ^ 2 * (∑ u ∈ Ioo a b, positionPhase p u) + positionPhase p b := by
  have hs : Icc a b = insert a (insert b (Ioo a b)) := by
    grind
  have hi : (∑ u ∈ Ioo a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      (c : ℂ) ^ 2 * ∑ u ∈ Ioo a b, positionPhase p u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    grind
  grind

/-- The single-gap geometric identity in the exact exponential convention of the wave. -/
theorem sum_gap_geometric (hp : z p ≠ 1) :
    (∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      L c (z p) * positionPhase p a + M c (z p) * positionPhase p b := by
  let d := (b - a - 1).toNat
  have hb : b = a + (d : ℤ) + 1 := by omega
  have hphase : positionPhase p b = positionPhase p a * (z p) ^ (d + 1) := by
    rw [hb, show a + (d : ℤ) + 1 = a + ((d + 1 : ℕ) : ℤ) by omega,
      positionPhase_add, positionPhase_nat]
  rw [sum_gap_endpoint_weights c p hab, hb, sum_positionPhase_Ioo,
    geom_sum_eq hp, positionPhase_add, positionPhase_one]
  have hb' : positionPhase p (a + (d : ℤ) + 1) = positionPhase p a * (z p) ^ (d + 1) := by
    simp_all
  rw [hb', pow_succ]
  grind [z, L, M]
end

end PottsDiscontinuity.BetheAnsatz
