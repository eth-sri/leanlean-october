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
  push_cast
  ring

@[simp] theorem positionPhase_one : positionPhase p 1 = z p := by
  simp [positionPhase, z]

theorem positionPhase_nat (d : ℕ) : positionPhase p d = z p ^ d := by
  rw [positionPhase, z, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- An open integer interval is a shifted natural geometric sum. -/
theorem sum_positionPhase_Ioo (a : ℤ) (d : ℕ) :
    (∑ u ∈ Ioo a (a + (d : ℤ) + 1), positionPhase p u) =
      positionPhase p (a + 1) * ∑ j ∈ range d, z p ^ j := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => a + (j : ℤ) + 1)
  · intro j hj
    have hj' := mem_range.mp hj
    simp only [mem_Ioo]
    constructor <;> omega
  · simp
  · intro u hu
    obtain ⟨hl, hr⟩ := mem_Ioo.mp hu
    refine ⟨(u - a - 1).toNat, ?_, ?_⟩
    · apply mem_range.mpr
      omega
    · omega
  grind [positionPhase_add, positionPhase_nat]

end

/-- The lower endpoint has weight 1, the upper endpoint `b`, and the
interior of the gap `d`. These independent weights let us move the spectral
pole without moving the Bethe roots. -/
def gapPointWeight (b d : ℂ) (l u y : ℤ) : ℂ :=
  if y = l then 1 else if y = u then b else d

noncomputable def gapLeft (d z : ℂ) : ℂ := 1 + d * z / (1-z)
noncomputable def gapRight (b d z : ℂ) : ℂ := b - d / (1-z)

/-- Separate the two endpoints from the interior weighted sum. -/
theorem sum_gap_endpoint_weights (B D : ℂ) (p : ℝ) {a b : ℤ} (hab : a < b) :
    (∑ u ∈ Icc a b, gapPointWeight B D a b u * positionPhase p u) =
      positionPhase p a + D * (∑ u ∈ Ioo a b, positionPhase p u) + B * positionPhase p b := by
  have hs : Icc a b = insert a (insert b (Ioo a b)) := by
    grind
  have ha : a ∉ insert b (Ioo a b) := by simp_all
  have hb : b ∉ Ioo a b := by simp
  rw [hs, Finset.sum_insert ha, Finset.sum_insert hb]
  have hi : (∑ u ∈ Ioo a b, gapPointWeight B D a b u * positionPhase p u) =
      D * ∑ u ∈ Ioo a b, positionPhase p u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have h := mem_Ioo.mp hu
    simp [gapPointWeight, h.1.ne', h.2.ne]
  rw [hi]
  simp [gapPointWeight, hab.ne']
  ring

/-- The single-gap geometric identity in the exact exponential convention of the wave. -/
theorem sum_gap_geometric (B D : ℂ) (p : ℝ) {a b : ℤ} (hab : a < b) (hp : z p ≠ 1) :
    (∑ u ∈ Icc a b, gapPointWeight B D a b u * positionPhase p u) =
      gapLeft D (z p) * positionPhase p a + gapRight B D (z p) * positionPhase p b := by
  let d := (b - a - 1).toNat
  have hb : b = a + (d : ℤ) + 1 := by omega
  have hphase : positionPhase p b = positionPhase p a * (z p) ^ (d + 1) := by
    rw [hb, show a + (d : ℤ) + 1 = a + ((d + 1 : ℕ) : ℤ) by push_cast; ring,
      positionPhase_add, positionPhase_nat]
  rw [sum_gap_endpoint_weights B D p hab, hb, sum_positionPhase_Ioo,
    geom_sum_eq hp, positionPhase_add, positionPhase_one]
  have hb' : positionPhase p (a + (d : ℤ) + 1) = positionPhase p a * (z p) ^ (d + 1) := by
    simp_all
  rw [hb', pow_succ]
  have hd := sub_ne_zero.mpr hp
  have hd' := sub_ne_zero.mpr hp.symm
  unfold gapLeft gapRight
  field_simp
  ring

end PottsDiscontinuity.BetheAnsatz
