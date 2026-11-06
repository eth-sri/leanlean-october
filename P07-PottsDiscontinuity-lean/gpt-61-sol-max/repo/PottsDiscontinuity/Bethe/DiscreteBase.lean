module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# The discrete Bethe equations at `Δ = -∞`

At the inverse parameter `ε=0`, the phase is `Θ(x,y)=y-x`.  This file proves
the explicit solution and uniqueness of the resulting finite system.
-/

@[expose] public section



namespace PottsDiscontinuity.Bethe

/-- A symmetric vector has total sum zero. -/
theorem sum_eq_zero_of_mem_R_n_sym {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ R_n_sym n) :  ∑ j : Fin n, p j  = 0 := by
  have hs   := Trans.trans (Trans.trans (Eq.symm (Equiv.sum_comp Fin.revPerm p)) (Finset.sum_congr rfl fun j hj => hp j))
                                                          (Eq.mpr (congrArg (fun _a => _a = -Finset.univ.sum p) (Finset.sum_neg_distrib p)) (Eq.refl (-Finset.univ.sum p)))
  linarith

/-- The limiting Bethe equations obtained by setting `Θ(x,y)=y-x`. -/
def DiscreteBetheEquationAtInfinity (N n : ℕ) (p : Fin n → ℝ)  :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * discreteBetheIndex n j - ∑ k : Fin n, (p k - p j)

/-- Explicit solution at `Δ=-∞`: `p_j=2πI_j/(N-n)`. -/
noncomputable def discreteBaseSolution (N n : ℕ) : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) : ℝ)

private theorem baseDenom_pos {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N) :
    0 < ((N - n : ℕ) : ℝ) := by
  
  exact_mod_cast Nat.sub_pos_of_lt (by omega)

private theorem baseDenom_ge_n {N n : ℕ} (hn : 2 * n ≤ N) :
    (n : ℝ) ≤ ((N - n : ℕ) : ℝ) := by
  
  exact_mod_cast  by omega 

private theorem discreteBetheIndex_abs_bound (n : ℕ) (j : Fin n) :
    |discreteBetheIndex n j| ≤ ((n : ℝ) - 1) / 2 := by
  
  have hj1 :  j.val  + 1 ≤ (n : ℝ) := by
    
    exact_mod_cast  Nat.succ_le_of_lt j.isLt 
  
  apply abs_le.mpr
  constructor <;> dsimp [discreteBetheIndex] <;> linarith

section

variable {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N)
include hN hn

/-- The explicit limiting solution belongs to the ordered symmetric configuration space. -/
theorem discreteBaseSolution_mem_S_n  :
    discreteBaseSolution N n ∈ S_n n := by
  have hD  := baseDenom_pos hN hn
  have hDge  := baseDenom_ge_n hn
  constructor
  · intro j
    
    have hI := discreteBetheIndex_abs_bound n j
    
    
    
    have hlt :
        |2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) )| < Real.pi := by
      rw [(by
             rw [abs_div, abs_mul, abs_of_pos (by positivity ), abs_of_pos hD] :
        |2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) )| =
           2 * Real.pi * |discreteBetheIndex n j|  / ((N - n : ℕ) ))]
      exact (div_lt_iff₀ hD).2 (by
                                  nlinarith [mul_lt_mul_of_pos_left (by
                                                                       nlinarith : 2 * |discreteBetheIndex n j| < ((N - n : ℕ) )) Real.pi_pos])
    have hbounds := abs_lt.mp hlt
    exact ⟨hbounds.left,
      hbounds.right⟩
  constructor
  · intro i j hij
    
    
    apply (div_lt_div_iff₀ hD hD).2
    have hnum : 2 * Real.pi * discreteBetheIndex n i <
        2 * Real.pi * discreteBetheIndex n j :=
      mul_lt_mul_of_pos_left (by
                                simp_all [discreteBetheIndex]) (by positivity)
    nlinarith 
  · 
    intro j
    simp only [discreteBaseSolution, discreteBetheIndex_rev]
    ring

/-- The explicit vector is a solution of the limiting equations. -/
theorem discreteBaseSolution_solves_at_infinity  :
    DiscreteBetheEquationAtInfinity N n (discreteBaseSolution N n) := by
  
  
  have hpsum := sum_eq_zero_of_mem_R_n_sym (by
                                              change ∀ j, discreteBaseSolution N n (Fin.rev j) = -discreteBaseSolution N n j
                                              intro j
                                              simp only [discreteBaseSolution, discreteBetheIndex_rev]
                                              ring)
  have hNdecomp :  N  =  (N - n : ℕ)  + (n : ℝ) := by
    
    exact_mod_cast (Nat.sub_add_cancel (by omega : n ≤ N)).symm
  have hgap (j : Fin n) :
       ∑ k : Fin n, (discreteBaseSolution N n k - discreteBaseSolution N n j)  =
        - n  * discreteBaseSolution N n j := by
    simp_all
  intro j
  rw [hgap, discreteBaseSolution, hNdecomp]
  field_simp [(baseDenom_pos hN hn).ne']
  ring

end

end PottsDiscontinuity.Bethe
