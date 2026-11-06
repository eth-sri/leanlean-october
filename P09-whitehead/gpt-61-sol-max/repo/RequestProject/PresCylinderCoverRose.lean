import Mathlib.Tactic

import RequestProject.StrictSubposetChains
import RequestProject.NormalizedStrictBoundary
import RequestProject.PresCylinderCoverCycles

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

def cylinderCoverRoseSet  := {p | ∃ x : Rose α, f p = cylIn (aHom w) x}

theorem cylinderCoverCollapse_mem_rose (p : P) :
    cylinderCoverCollapse w hf p ∈ cylinderCoverRoseSet w f :=
  ⟨cylRetr (aHom w) (f p), cylinderCoverCollapse_projection w hf p⟩

/-- Every surviving genuine edge of a collapsed finite chain lies in the actual rose preimage. -/
theorem cylinderCoverCollapsedChain_support_rose (c : StrictOrdEdge P →₀ ℤ) :
    ∀ e ∈ (normalizedStrictChain1 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c).support,
      e.1.1 ∈ cylinderCoverRoseSet w f ∧ e.1.2 ∈ cylinderCoverRoseSet w f := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    grind [Finsupp.support_add]
  | single t n =>
    intro e he
    rw [normalizedStrictChain1_single] at he
    by_cases h : cylinderCoverCollapse w hf t.1.1 = cylinderCoverCollapse w hf t.1.2
    · simp [normalizeOrdEdge, h] at he
    · simp only [normalizeOrdEdge, dif_neg h] at he
      let r : StrictOrdEdge P := ⟨(cylinderCoverCollapse w hf t.1.1,
        cylinderCoverCollapse w hf t.1.2),
        lt_of_le_of_ne (cylinderCoverCollapse_monotone w hf t.2.le) h⟩
      change e ∈ (n • Finsupp.single r (1 : ℤ)).support at he
      have hr : e = r := by
        by_contra hn
        have hz : (n • Finsupp.single r (1 : ℤ)) e = 0 := by simp [Ne.symm hn]
        exact (Finsupp.mem_support_iff.mp he) hz
      subst e
      exact ⟨cylinderCoverCollapse_mem_rose w f hf t.1.1,
        cylinderCoverCollapse_mem_rose w f hf t.1.2⟩

end FiniteChains.PresModel
