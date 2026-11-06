module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Adj.Weight
import Erdos821.P3Rows.GhostRows

public import Erdos821.P3Clean.Laws
public import Erdos821.Leaves.Arith

/-! Positivity and a uniform density ratio for the tilted active laws. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

alias visitQ_pos := _root_.Erdos821.P3Adj.visitQ_pos

alias visitQ_lt_one := _root_.Erdos821.S2Core.visitQ_lt_one

theorem eta_nonneg  F   n   i  : 0 ≤ eta F n i :=
  sub_nonneg.mpr (visitQ_lt_one F n i).le

theorem eta_le_one  F   n   i  : eta F n i ≤ 1 :=
  sub_le_self 1 (visitQ_pos F n i).le

theorem eta_sum_bounds  F   n  :
    0 ≤ (∑ i : Fin (n + 1), eta F n i) ∧
      (∑ i : Fin (n + 1), eta F n i) ≤ (n + 1 : ℕ) := by
  refine ⟨Finset.sum_nonneg (fun i _ => eta_nonneg F n i), ?_⟩
  calc
    _ ≤ ∑ _ : Fin (n + 1), (1 : ℝ) := Finset.sum_le_sum (fun i _ => eta_le_one F n i)
    _ = _ := by simp

theorem baselinePrime_bounds  F   n p  (hp : 0 < p)
    (hn : 2 * (n + 1) ≤ p) :
    0 < baselinePrime F n p ∧ 1 ≤ (baselinePrime F n p)⁻¹ ∧
      (baselinePrime F n p)⁻¹ ≤ 1 + 2 * ((n + 1 : ℕ) : ℝ) / p := by
  obtain ⟨he0, he1⟩ := eta_sum_bounds F n
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have he2 : 2 * (∑ i : Fin (n + 1), eta F n i) ≤ (p : ℝ) := by
    have hnR : 2 * ((n + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hn
    linarith
  have h := tilted_density_bound (p : ℝ) (∑ i : Fin (n + 1), eta F n i) hpR he0 he2
  have heq : baselinePrime F n p = 1 - (∑ i : Fin (n + 1), eta F n i) / (p : ℝ) := by
    unfold baselinePrime
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq]
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  gcongr <;> first | assumption | positivity | linarith

theorem tiltedMu_eq_mu_mul  F   P   n 
     g   p  :
    tiltedMu F P n g p = P.mu g p * (baselinePrime F n p.val)⁻¹ := by
  unfold tiltedMu PrimeGroups.mu
  rw [mul_inv_rev]
  ring

end Erdos821.P3Clean
