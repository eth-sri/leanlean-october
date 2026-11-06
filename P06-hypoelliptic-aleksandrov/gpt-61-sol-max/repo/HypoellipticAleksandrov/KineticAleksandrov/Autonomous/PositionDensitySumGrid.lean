module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlap
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumKernel

/-! # Embedding the source grid into the two-index integer lattice -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal Classical

/-- Include the nonnegative time-bin lattice in the full two-index group. -/
def positionIndexEmbedding (a : ℕ × ℤ) : ℤ × ℤ := ((a.1 : ℤ), a.2)

/-- The source grid embedding is injective. -/
theorem positionIndexEmbedding_injective : Function.Injective positionIndexEmbedding := (fun ⦃a b⦄ h => Prod.ext (id (fun he => cast Nat.cast_inj._simp_1 he) (congrArg Prod.fst h)) (congrArg (fun a => a.2) h))

variable (nu : Measure Point) (c : Clock)

variable (s x : ℝ)

/-- Extend the source starting masses by zero to negative time indices. -/
def positionMassSequence   (a : ℤ × ℤ) : ℝ≥0∞ :=
  if 0 ≤ a.1 then nu (enlargedStartCell c s x a.1.toNat a.2) else 0

/-- On the source grid the extended mass sequence is exactly the starting-cell mass. -/
theorem positionMassSequence_embed   (a : ℕ × ℤ) :
    positionMassSequence nu c s x (positionIndexEmbedding a) =
      nu (enlargedStartCell c s x a.1 a.2) := by
  rfl

/-- The extension by zero preserves the q-power sum of the starting masses. -/
theorem positionMassSequence_power_sum  (s x q : ℝ)
    (hq : 0 < q) :
    (∑' a : ℤ × ℤ, positionMassSequence nu c s x a ^ q) =
      ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod',
    tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hpos : (∑' n : ℕ, ∑' k : ℤ, positionMassSequence nu c s x ((n : ℤ), k) ^ q) =
      ∑' n : ℕ, ∑' k : ℤ, nu (enlargedStartCell c s x n k) ^ q := by
    rfl
  have hneg : (∑' n : ℕ, ∑' k : ℤ,
      positionMassSequence nu c s x (-((n : ℤ) + 1), k) ^ q) = 0 := by
    have hn (n : ℕ) : ¬(0 ≤ -((n : ℤ) + 1)) := by omega
    simp only [positionMassSequence, hn, ite_false, ENNReal.zero_rpow_of_pos hq, tsum_zero]
  rw [hpos, hneg, add_zero]

/-- The source overlap weight is bounded by the same summable two-index majorant. -/
theorem positionOverlapWeight_le (c₀ : ℝ) (hc₀ : 0 < c₀) (i j : ℕ) (ell k : ℤ) :
    positionOverlapWeight c₀ i j ell k ≤ ENNReal.ofReal (Real.exp (2 * c₀)) *
      ENNReal.ofReal (positionYoungKernel (c₀ / 12)
        (positionIndexEmbedding (i, ell) - positionIndexEmbedding (j, k))) := by
  unfold positionOverlapWeight
  split
  · rename_i hover
    have hj : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hover.1
    have hh  := sub_nonneg.mpr hj
    have h := position_overlap_majorant c₀ _
      _ hc₀ hh hover.2
    apply (ENNReal.ofReal_le_ofReal h).trans_eq
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [positionYoungKernel, positionIndexEmbedding, Prod.fst_sub, Prod.snd_sub,
      Int.cast_sub, Int.cast_natCast]
  · exact zero_le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
