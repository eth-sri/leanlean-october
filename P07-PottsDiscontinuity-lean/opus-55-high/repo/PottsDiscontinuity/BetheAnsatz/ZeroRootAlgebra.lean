module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Bethe products with one zero root

The zero-root Bethe equation and equation (19) imply equality of the products
of L and M over the remaining roots. This is the cancellation in the T₀ terms.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The L and M products over all nonzero roots agree at a zero-root Bethe solution. -/
theorem prod_L_eq_prod_M_of_zero {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, L c (z (p j))) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
  have hh := hBE l
  rw [hpl, ← add_sum_erase _ _ (mem_univ l), hpl, Bethe.theta_self, zero_add, Nat.add_sub_cancel,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hh
  have hprod := Complex.exp_sum (univ.erase l) fun j => I * (Bethe.theta (anisotropy c) 0 (p j) : ℂ)
  rw [← mul_sum, ← Complex.ofReal_sum, prod_congr rfl fun j hj => exp_I_theta_zero_eq_neg_L_div_M_of_mem hc (hp j)
    fun h => ne_of_mem_erase hj (hinj (h.trans hpl.symm))] at hprod
  simp only [neg_div, prod_neg, prod_div_distrib, card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin,
    Nat.add_sub_cancel] at hprod
  have hE := Complex.exp_add (I * ((∑ j ∈ univ.erase l, Bethe.theta (anisotropy c) 0 (p j) : ℝ) : ℂ))
    (-(I * ((∑ j ∈ univ.erase l, Bethe.theta (anisotropy c) 0 (p j) : ℝ) : ℂ)))
  rw [add_neg_cancel, Complex.exp_zero] at hE
  apply eq_of_div_eq_one
  grind

end PottsDiscontinuity.BetheAnsatz
