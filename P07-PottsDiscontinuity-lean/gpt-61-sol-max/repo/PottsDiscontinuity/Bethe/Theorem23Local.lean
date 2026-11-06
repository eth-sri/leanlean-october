module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Derivative

/-! # Local analytic Bethe branches at regular solutions -/

@[expose] public section




namespace PottsDiscontinuity.Bethe

theorem discreteCoordinateResidual_zero_iff {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidual Δ N n q = 0 ↔
      DiscreteBetheEquation Δ N n (discreteSymLift n q) := by
  have hsym := discreteSymLift_mem n q
  
  constructor
  · intro h
    
    apply (discreteBetheMap_fixed_iff_equation hN _).1
     
    exact (sub_eq_zero.mp (discreteSym_ext ((R_n_sym n).sub_mem hsym (discreteBetheMap_mem_R_n_sym Δ N n _ hsym)) (Submodule.zero_mem (R_n_sym n)) (congrFun h))).symm
  · intro h
    
    funext i
    change discreteSymLift n q (discreteHalfIndex n i) -
      discreteBetheMap Δ N n (discreteSymLift n q) (discreteHalfIndex n i) = 0
    rw [ (discreteBetheMap_fixed_iff_equation hN _).2 h , sub_self]

end PottsDiscontinuity.Bethe
