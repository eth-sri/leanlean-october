module
public import Mathlib.Tactic

public import Erdos821.S34.CellSup
public import Erdos821.S34.OwnedLeafProofs

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

open Blueprint.Analytic

section
variable (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ) (h ξ : ℝ)

theorem kernel_log_localization    
        (hh : 0 < h)  D X 
    (hne : cellKernel G k Q h ξ D X ≠ 0) :
    |Real.log D - Real.log X| < h := by
  have heq : cell h D = cell h X := by
    unfold cellKernel at hne
    simp_all
  have hDlo := Int.floor_le (Real.log D / h)
  have hDhi := Int.lt_floor_add_one (Real.log D / h)
  have hXlo := Int.floor_le (Real.log X / h)
  have hXhi := Int.lt_floor_add_one (Real.log X / h)
  change ⌊Real.log D / h⌋ = ⌊Real.log X / h⌋ at heq
  rw [heq] at hDlo hDhi
  have hDlo' := (le_div_iff₀ hh).mp hDlo
  have hDhi' := (div_lt_iff₀ hh).mp hDhi
  have hXlo' := (le_div_iff₀ hh).mp hXlo
  have hXhi' := (div_lt_iff₀ hh).mp hXhi
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem kernel_l1_bound    
        (hξ : 0 < ξ)  X  :
    (∑ D : Tuple G k, tupleWeight G k D * ‖cellKernel G k Q h ξ (product G k D) X‖) ≤
      (Q : ℝ) ^ 2 := by
  let ν := cellMass G k h (cell h X)
  have hw (D : Tuple G k) : 0 ≤ tupleWeight G k D :=
    Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) k D
  by_cases hret : ξ ≤ ν
  · have hν : 0 < ν := hξ.trans_le hret
    have hpoint (D : Tuple G k) :
        ‖cellKernel G k Q h ξ (product G k D) X‖ ≤
          if cell h (product G k D) = cell h X then (Q : ℝ) ^ 2 / ν else 0 := by
      by_cases hm : cell h (product G k D) = cell h X
      · have hk : cellKernel G k Q h ξ (product G k D) X =
            cellKernel G k Q h ν (product G k D) X := by
          grind [cellKernel, cellMass, cell]
        rw [ite_eq_left hm, hk]
        exact cell_kernel_sup_proof G k Q h ν hν (product G k D) X
      · simp [cellKernel, hm]
    calc
      _ ≤ ∑ D : Tuple G k, tupleWeight G k D *
          (if cell h (product G k D) = cell h X then (Q : ℝ) ^ 2 / ν else 0) :=
        Finset.sum_le_sum fun D _ => mul_le_mul_of_nonneg_left (hpoint D) (hw D)
      _ = ((Q : ℝ) ^ 2 / ν) * ν := by
        dsimp [ν, cellMass]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> ring
      _ = _ := div_mul_cancel₀ _ hν.ne'
  · have hz (D : Tuple G k) : cellKernel G k Q h ξ (product G k D) X = 0 := by
      grind [cellKernel, cellMass, cell]
    simp only [hz, norm_zero, mul_zero, Finset.sum_const_zero]
    positivity

end

end Erdos821.S34Core
