module
public import Mathlib.Tactic

public import Erdos821.P3Edge.RowFinite
public import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}



lemma absKernel_eq (A : Model F P J m)  n   rho theta   i 
     s t  :
    absoluteMemoryEdgeKernel A n rho theta i .all s t =
      edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
        if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := rfl

section
variable (A : Model F P J m) {n : ℕ} (rho theta : ℝ) (i : Fin n) (s : P.MemoryState (J + F.ell))

lemma row_kernel_support_subset        
      :
    {t | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} ⊆
      {t | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := by
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  rw [absKernel_eq] at ht
  
  have hsum : (∑ c : EdgeChoice A s, if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) ≠ 0 := by
    intro h0
    apply ht
    rw [h0, mul_zero]
  by_contra hnone
  push Not at hnone
  have hall : ∀ c : EdgeChoice A s, (if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) = 0 := by
    intro c
    have hn := hnone c
    simp [hn]
  have hsum0 : (∑ c : EdgeChoice A s, if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) = 0 := by
    simp [hall]
  exact hsum hsum0

lemma row_kernel_set_finite        
      :
    Set.Finite {t | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} := (row_valid_set_finite A i s).subset (row_kernel_support_subset A rho theta i s)

end

lemma row_summable (F : FixedData) (r : MemoryParameters F)
    (A : Model F P J m)  n   theta   i 
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) := by
  classical
  have hfin := row_kernel_set_finite A r.rho theta i s
  
  have hsup : Function.support (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) ⊆
      {t | absoluteMemoryEdgeKernel A n r.rho theta i .all s t ≠ 0} := by
    intro t ht
    simp only [Function.support, Set.mem_ofPred_eq] at ht ⊢
    intro h0
    apply ht
    rw [h0]
    simp
  have hfin2 : Function.HasFiniteSupport (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) :=
    hfin.subset hsup
  exact summable_of_hasFiniteSupport hfin2

end Erdos821.P3Edge
