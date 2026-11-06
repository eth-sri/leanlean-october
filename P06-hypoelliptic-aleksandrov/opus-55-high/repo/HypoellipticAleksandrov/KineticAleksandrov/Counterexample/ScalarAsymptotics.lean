module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptotics
import Mathlib.Tactic

/-!
# The positive scalar tail

The scalar remainder follows from the internally proved finite-order U expansion.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics

/-- Exact rescaling of the positive scalar tail's power. -/
theorem scalar_tail_power (s D p : ℝ) (hs : 0 < s) (hD : 0 < D) :
    Real.rpow (s ^ 3 / D) p = Real.rpow D (-p) * Real.rpow s (3 * p) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (pow_nonneg hs.le _) hD.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hs.le, Real.rpow_neg hD.le]
  ring

/-- Positive cubic rescaling sends the positive scalar ray to positive infinity. -/
theorem tendsto_scalar_tail_argument (D : ℝ) (hD : 0 < D) :
    Tendsto (fun s : ℝ => s ^ 3 / D) atTop atTop := (tendsto_pow_atTop (by decide)).atTop_div_const hD

/-- Pull back a power remainder by the positive cubic change of variable. -/
theorem isBigO_comp_scalar_tail (e : ℝ → ℝ) (p D : ℝ) (hD : 0 < D)
    (he : IsBigO atTop e (fun z => Real.rpow z p)) :
    IsBigO atTop (fun s => e (s ^ 3 / D)) (fun s => Real.rpow s (3 * p)) := by
  obtain ⟨C, hb⟩ := isBigO_iff.mp he
  refine isBigO_iff.mpr ⟨C * Real.rpow D (-p), ?_⟩
  filter_upwards [(tendsto_scalar_tail_argument D hD).eventually hb,
    eventually_gt_atTop (0)] with s hs hs0
  rw [scalar_tail_power s D p hs0 hD] at hs
  simp only [Real.rpow_eq_pow] at hs ⊢
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_pos_of_pos hD _).le] at hs
  linarith

/-- The positive piece has the source leading coefficient and cubic-order remainder. -/
theorem Fplus_asymptotic (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop
      (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
  have hD : 0 < 9 * Lam := mul_pos (by norm_num) hLam
  have hu := Kummer.UNr_expansion gamma.negative 1
  obtain ⟨C, hb⟩ := isBigO_iff.mp hu
  refine isBigO_iff.mpr ⟨C * Real.rpow (9 * Lam) (1 - gamma.1), ?_⟩
  have he := (tendsto_scalar_tail_argument _ hD).eventually hb
  filter_upwards [he, eventually_gt_atTop (0)] with s hs hs0
  have hm : Kummer.uExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / (9 * Lam)) =
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1) := by
    simp only [Kummer.uExpansion, Finset.sum_range_one, pow_zero, Kummer.poch_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, one_div, inv_one, neg_neg]
    simpa using scalar_tail_power s _ gamma.1 hs0 hD
  have hp : Real.rpow (s ^ 3 / (9 * Lam)) (gamma.1 - 1) =
      Real.rpow (9 * Lam) (1 - gamma.1) * Real.rpow s (3 * gamma.1 - 3) := by
    rw [scalar_tail_power s _ _ hs0 hD]
    ring
  norm_num only [Nat.cast_one] at hs
  simp only [ScalarGamma.negative, neg_neg, hm, hp, norm_mul] at hs
  simp only [Real.rpow_eq_pow] at hs ⊢
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hD _).le] at hs
  simpa only [Fplus, Real.rpow_eq_pow, ScalarGamma.negative,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hs0 _).le,
    mul_assoc] using hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
