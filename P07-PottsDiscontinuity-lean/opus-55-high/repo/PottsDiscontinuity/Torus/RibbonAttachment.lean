module

public import PottsDiscontinuity.Torus.RibbonEdges

/-!
# Attaching one indexed ribbon

Changing one primal edge composes the boundary permutation with the transposition
of its two ends. This is the combinatorial cut-and-join operation needed to count
boundary components under ribbon attachment.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (A : RCConfig N M) (v : Fin N × Fin M)
/-- Toggle one indexed primal edge. -/
def toggleEdge  : RCConfig N M :=
  Function.update A v (!A v)

@[simp] theorem toggleEdge_at  :
    toggleEdge A v v = !A v := by simp only [toggleEdge, Function.update_self]
end

theorem toggleEdge_away (A : RCConfig N M) {v w : Fin N × Fin M} (h : w ≠ v) :
    toggleEdge A v w = A w := Function.update_of_ne h _ _


section
variable (hN : Even N) (hM : Even M)
/-- The transposition of the two distinct slots of one indexed ribbon. -/
def ribbonEndSwap (v : Fin N × Fin M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  Equiv.swap (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))

theorem ribbonEndSwap_end (v w : Fin N × Fin M) (b : Bool) :
    ribbonEndSwap hN hM v (ribbonEndEquiv hN hM (w, b)) =
      ribbonEndEquiv hN hM (w, if w = v then !b else b) := by
  by_cases hw : w = v
  · subst w
    cases b <;> simp only [ribbonEndSwap, Equiv.swap_apply_left,
      Equiv.swap_apply_right, ite_true, Bool.not_false, Bool.not_true]
  · have h₀ : ribbonEndEquiv hN hM (w, b) ≠ ribbonEndEquiv hN hM (v, false) := by
      simp_all
    have h₁ : ribbonEndEquiv hN hM (w, b) ≠ ribbonEndEquiv hN hM (v, true) := by
      simp_all
    grind [ribbonEndSwap]
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (v : Fin N × Fin M)
theorem ribbonEdgePairing_toggle  :
    ribbonEdgePairing hN hM (toggleEdge A v) =
      ribbonEndSwap hN hM v * ribbonEdgePairing hN hM A := by
  apply Equiv.ext
  intro d
  obtain ⟨⟨w, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [Equiv.Perm.mul_apply, ribbonEdgePairing_end, ribbonEdgePairing_end,
    ribbonEndSwap_end]
  by_cases hw : w = v
  · simp_all
  simp_all [toggleEdge_away]

/-- Toggling an indexed primal edge cuts or joins its two boundary strands. -/
theorem ribbonBoundary_toggle  :
    ribbonBoundary hN hM (toggleEdge A v) =
      ribbonEndSwap hN hM v * ribbonBoundary hN hM A := by
  apply Equiv.ext
  intro d
  change ribbonEdgePairing hN hM (toggleEdge A v) (faceRotation hN hM d) = _
  rw [ribbonEdgePairing_toggle]
  rfl
end

end PottsDiscontinuity.Torus
