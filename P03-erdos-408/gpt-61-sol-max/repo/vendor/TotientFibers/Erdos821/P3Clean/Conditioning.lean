module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Descent.FirstPriorityEnergy

public import Erdos821.P3Clean.Damping
public import Erdos821.P3Clean.SmallFibres
public import Erdos821.Leaves.Damped

/-! The Cauchy estimate for a small-conditioning map, with its fibre count explicit. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem norm_sum_sq_le_card {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖f a‖ ^ 2 := by solve_by_elim [_root_.OAI.SevenEighths.InverseMoment.priority_norm_sum_sq]

theorem conditioning_normSq_bound {α β : Type*} [Fintype β]
    (s : Finset α) (projection : α → β) (u : β → ℂ) (C : ℝ)
    (hC : ∀ d, ‖u d‖ ^ 2 * ((s.filter (fun a => projection a = d)).card : ℝ) ≤ C)
    (f : α → ℂ) :
    (∑ d : β, ‖u d * ∑ a ∈ s.filter (fun a => projection a = d), f a‖ ^ 2) ≤
      C * ∑ a ∈ s, ‖f a‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ d : β, C * ∑ a ∈ s.filter (fun a => projection a = d), ‖f a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul, mul_pow]
      calc
        _ ≤ ‖u d‖ ^ 2 *
            (((s.filter (fun a => projection a = d)).card : ℝ) *
              ∑ a ∈ s.filter (fun a => projection a = d), ‖f a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_sum_sq_le_card _ f) (sq_nonneg _)
        _ = (‖u d‖ ^ 2 * ((s.filter (fun a => projection a = d)).card : ℝ)) *
            ∑ a ∈ s.filter (fun a => projection a = d), ‖f a‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hC d)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise s projection (fun a => ‖f a‖ ^ 2)

/-- The only factorial exponent in the small-conditioning map is ell. -/
theorem small_conditioning_multiplier_uniform (F : FixedData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M z : ℕ) (V : ℝ), M ≤ z → F.vMin ≤ V →
      V ^ (-(F.ell : ℤ)) * ((z - M + F.ell).descFactorial F.ell : ℝ) *
        F.q ^ ((z : ℝ) - (M : ℝ)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    damped_factorial_bound F.q F.vMin F.q_pos F.q_lt F.vMin_pos F.ell
  refine ⟨C, hC, ?_⟩
  intro M z V hMz hV
  have hq : F.q ^ ((z - M : ℕ) : ℝ) ≤ F.q ^ (((z - M : ℕ) : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_ge F.q_pos F.q_lt.le
    
    linarith
  have hVpos : 0 < V := F.vMin_pos.trans_le hV
  rw [← Nat.cast_sub hMz]
  exact (mul_le_mul_of_nonneg_left hq
    (mul_nonneg (zpow_nonneg hVpos.le _) (Nat.cast_nonneg _))).trans
    (hbound F.ell (z - M) V le_rfl hV)

theorem small_prefix_multiplier_uniform (F : FixedData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PrimeGroups) (g : P.Group) (J : ℕ)
      (y : (p : P.Prime g) → ZMod p.val) (d : Fin J → P.Prime g),
      F.vMin ≤ P.V g →
        (P.V g) ^ (-(F.ell : ℤ)) * ((smallPrefixFibre J F.ell y d).card : ℝ) *
          F.q ^ (((Finset.univ.filter (fun p : P.Prime g => y p = 0)).card : ℝ) -
            ((J + F.ell : ℕ) : ℝ)) ≤ C := by
  classical
  obtain ⟨C, hC, hbound⟩ := small_conditioning_multiplier_uniform F
  refine ⟨C, hC, ?_⟩
  intro P g J y d hV
  by_cases hs : (smallPrefixFibre J F.ell y d).Nonempty
  · obtain ⟨hd, hy, hz⟩ := smallPrefixFibre_nonempty J F.ell y d hs
    have hc := smallPrefixFibre_card J F.ell y d hd hy
    have heq : (Finset.univ.filter (fun p : P.Prime g => y p = 0)).card - J =
        (Finset.univ.filter (fun p : P.Prime g => y p = 0)).card - (J + F.ell) + F.ell := by
      omega
    rw [heq] at hc
    have hcast : ((smallPrefixFibre J F.ell y d).card : ℝ) ≤
        (((Finset.univ.filter (fun p : P.Prime g => y p = 0)).card -
          (J + F.ell) + F.ell).descFactorial F.ell : ℝ) := by exact_mod_cast hc
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcast (zpow_nonneg (F.vMin_pos.trans_le hV).le _))
      (Real.rpow_nonneg F.q_pos.le _)).trans (hbound _ _ _ hz hV)
  · have hzero := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa only [hzero, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul] using hC.le

def normalizedSmallCoefficient (F : FixedData) (J : ℕ) (V : ℝ) (z : ℕ)  :=
  Real.sqrt (V ^ (-(F.ell : ℤ)) * F.q ^ ((z : ℝ) - ((J + F.ell : ℕ) : ℝ)))

end Erdos821.P3Clean
