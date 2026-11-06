module
public import Mathlib

public import PottsDiscontinuity.Torus.PermutationSurgery
public import PottsDiscontinuity.Torus.RibbonAttachment
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-!
# Boundary counts under ribbon surgery

The general permutation cut-and-join theorem applies to the actual RC loops.
Every boundary lies within a single ribbon component, so joining two components
necessarily joins two distinct boundary cycles.
-/

@[expose] public section



namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M)
include hN hM

theorem ribbonEnds_ne  (v : Fin N × Fin M) :
    ribbonEndEquiv hN hM (v, false) ≠ ribbonEndEquiv hN hM (v, true) := by
                                                                          simp_all

section

variable (A : RCConfig N M)


theorem permutationCycleCount_ribbonBoundary 
     :
    permutationCycleCount (ribbonBoundary hN hM A) = rcLoopCount hN hM A :=
  card_ribbonBoundaryComponent hN hM A

theorem ribbonConnected_boundary_step 
     (d : DirectedDart (checkerArrows N M)) :
    RibbonConnected hN hM A d (ribbonBoundary hN hM A d) := Relation.EqvGen.trans _ _ _
                                                        (Relation.EqvGen.rel _ _ (Or.inl  Equiv.Perm.SameCycle.rfl.apply_right ))
                                                        (Relation.EqvGen.rel _ _ (Or.inr rfl))

/-- Each boundary cycle is contained in a connected component of the open ribbon subgraph. -/
theorem ribbonConnected_of_boundary_sameCycle 
     {d e : DirectedDart (checkerArrows N M)}
    (h : (ribbonBoundary hN hM A).SameCycle d e) : RibbonConnected hN hM A d e := Quotient.exact
                                                                                    (sameCycle_invariant (ribbonBoundary hN hM A) (Quotient.mk (Relation.EqvGen.setoid (ribbonAdjacent hN hM A)))
                                                                                      (fun x =>
                                                                                        Quotient.sound (Relation.EqvGen.symm x ((ribbonBoundary hN hM A) x) (ribbonConnected_boundary_step hN hM A x)))
                                                                                      h)

theorem rcLoopCount_toggle_split 
     (v : Fin N × Fin M)
    (h : (ribbonBoundary hN hM A).SameCycle
      (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))) :
    rcLoopCount hN hM (toggleEdge A v) = rcLoopCount hN hM A + 1 := by
  rw [← permutationCycleCount_ribbonBoundary, ribbonBoundary_toggle]
  exact (permutationCycleCount_swap_split _ (ribbonEnds_ne hN hM v) h).trans
    (congrArg (· + 1) (permutationCycleCount_ribbonBoundary hN hM A))

theorem rcLoopCount_toggle_join 
     (v : Fin N × Fin M)
    (h : ¬(ribbonBoundary hN hM A).SameCycle
      (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))) :
    rcLoopCount hN hM (toggleEdge A v) + 1 = rcLoopCount hN hM A := by
  rw [← permutationCycleCount_ribbonBoundary, ribbonBoundary_toggle]
  exact (permutationCycleCount_swap_join _ h).trans
    (permutationCycleCount_ribbonBoundary hN hM A)

end

end

end PottsDiscontinuity.Torus
