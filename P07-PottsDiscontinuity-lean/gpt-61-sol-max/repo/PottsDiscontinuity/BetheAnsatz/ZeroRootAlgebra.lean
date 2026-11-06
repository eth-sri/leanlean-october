module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Bethe products with one zero root

The zero-root Bethe equation and equation (19) imply equality of the products
of L and M over the remaining roots. This is the cancellation in the T₀ terms.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The L and M products over all nonzero roots agree at a zero-root Bethe solution. -/
theorem prod_L_eq_prod_M_of_zero {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
     ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, L c (z (p j))  =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
  let s  := univ.erase l
  let θ  := fun j => Bethe.theta (anisotropy c) 0 (p j)
  
  have heq :  1  = (-1 ) ^ n *
      Complex.exp (-(I * ( ∑ j ∈ s, θ j  : ℂ))) := by
    have hh := hBE l
    rw [hpl] at hh
    simpa [θ, ← (by
                   
                   simp [s, θ, hpl, Bethe.theta_self] :  ∑ j ∈ s, θ j  = ∑ j, θ j)] using hh
  
  
  
  
  have hphaseprod :  ∏ j ∈ s, Complex.exp (I *  θ j )  = (-1 ) ^ n := by
    rw [← Complex.exp_sum]
    have hcast :  ∑ j ∈ s, I *  θ j   = I *  ∑ j ∈ s, θ j  := by
      push_cast
      rw [← Finset.mul_sum]
    rw [hcast]
    exact  by
             calc
               _ = (Complex.exp (-(I * ( ∑ j ∈ s, θ j  : ℂ))) )⁻¹ := by
                 rw [Complex.exp_neg]
                 simp
               _ = (-1 ) ^ n := by
                 grind 
  
  
  
  exact (div_eq_one_iff_eq (by
                              apply Finset.prod_ne_zero_iff.mpr
                              intro j hj
                              have hjl  := (mem_erase.mp hj).1
                              
                              exact M_ne_zero hc (z_ne_one (hp j) (by
                                                                     grind)))).mp (by
                                                                                have hcalc :  ∏ j ∈ s, Complex.exp (I * (θ j : ℂ))  =
                                                                                    (-1 : ℂ) ^ n *
                                                                                      ((∏ j ∈ s, L c (z (p j))) /  ∏ j ∈ s, M c (z (p j)) ) := by
                                                                                  calc
                                                                                    _ = ∏ j ∈ s,  -L c (z (p j)) / M c (z (p j))  := prod_congr rfl (by
                                                                                                                                                       intro j hj
                                                                                                                                                       have hjl  := (mem_erase.mp hj).1
                                                                                                                                                       
                                                                                                                                                       exact exp_I_theta_zero_eq_neg_L_div_M_of_mem hc (hp j) (by
                                                                                                                                                                                                                 grind))
                                                                                    _ = ∏ j ∈ s,  (-1 : ℂ) * (L c (z (p j)) / M c (z (p j)))  := by
                                                                                      ring
                                                                                    _ = (∏ j ∈ s, (-1 : ℂ)) *  ∏ j ∈ s,  L c (z (p j)) / M c (z (p j))   :=
                                                                                      Finset.prod_mul_distrib
                                                                                    _ = _ := by
                                                                                      rw [Finset.prod_div_distrib]
                                                                                      simp [s, Finset.card_erase_of_mem (mem_univ l)]
                                                                                grind)

end PottsDiscontinuity.BetheAnsatz
