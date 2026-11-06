module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Geometric sums in an integer gap

Companion paper, equation `eq:EmptySetCalc`. Integer endpoints can be negative.
The only spectral restriction in this finite calculation is `z(p) ≠ 1`.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The exponential at one integer coordinate. -/
noncomputable def positionPhase (p : ℝ) (u : ℤ)  := Complex.exp (I * (p : ℂ) * (u : ℂ))

section

variable (p : ℝ)


theorem positionPhase_add  (a b : ℤ) :
    positionPhase p (a + b) = positionPhase p a * positionPhase p b := by
  unfold positionPhase
  rw [← Complex.exp_add]
  
  push_cast
  ring

@[simp] theorem positionPhase_one  : positionPhase p 1 = z p := by
  simp_all [positionPhase, z]

theorem positionPhase_nat  (d : ℕ) : positionPhase p d = z p ^ d := by
  rw [positionPhase, z, ← Complex.exp_nat_mul]
  
  push_cast
  ring

/-- An open integer interval is a shifted natural geometric sum. -/
theorem sum_positionPhase_Ioo  (a : ℤ) (d : ℕ) :
     ∑ u ∈ Ioo a (a + (d : ℤ) + 1), positionPhase p u  =
      positionPhase p (a + 1) * ∑ j ∈ range d, z p ^ j := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij  fun (j : ℕ) _ => a +  j  + 1 
  · simp_all
  · 
    omega
  · intro u hu
    obtain ⟨hl, hr⟩ := mem_Ioo.mp hu
    refine ⟨(u - a - 1).toNat, ?_, ?_⟩
    · apply mem_range.mpr
      omega
    · omega
  · grind [positionPhase_add, positionPhase_nat]

end

section

variable (c p : ℝ) {a b : ℤ} (hab : a < b)
include hab

/-- Separate the two endpoints from the interior weighted sum. -/
theorem sum_gap_endpoint_weights  :
     ∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u  =
      positionPhase p a + (c : ℂ) ^ 2 *  ∑ u ∈ Ioo a b, positionPhase p u  + positionPhase p b := by
  have hs : Icc a b = insert a (insert b (Ioo a b)) := by
    grind
  
  
  rw [hs, Finset.sum_insert (by simp [hab.ne]), Finset.sum_insert (by simp)]
  have hi :  ∑ u ∈ Ioo a b, (if u = a ∨ u = b then  1  else (c : ℂ) ^ 2) * positionPhase p u  =
       c  ^ 2 * ∑ u ∈ Ioo a b, positionPhase p u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    aesop
  rw [hi]
  simp only [true_or, or_true, ↓reduceIte]
  ring

/-- The single-gap geometric identity in the exact exponential convention of the wave. -/
theorem sum_gap_geometric  (hp : z p ≠ 1) :
     ∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u  =
      L c (z p) * positionPhase p a + M c (z p) * positionPhase p b := by
  let d := (b - a - 1).toNat
  have hb : b = a +  d  + 1 := by  omega
  have hphase : positionPhase p b = positionPhase p a *  z p  ^ (d + 1) := by
    rw [hb, show a +  d  + 1 = a +  (d + 1 : ℕ)  by push_cast; ring,
      positionPhase_add, positionPhase_nat]
  rw [sum_gap_endpoint_weights c p hab, hb, sum_positionPhase_Ioo,
    geom_sum_eq hp, positionPhase_add, positionPhase_one]
  
  rw [(by
         rw [← hb]
         exact hphase : positionPhase p (a + (d ) + 1) = positionPhase p a *  z p  ^ (d + 1))]
  
  
  unfold L M
  field_simp
  ring

end

end PottsDiscontinuity.BetheAnsatz
