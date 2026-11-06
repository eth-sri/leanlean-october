import RequestProject.StrictSubposetChains
import RequestProject.NormalizedStrictBoundary
import RequestProject.PresCylinderCoverCycles


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

def cylinderCoverRoseSet := {p | ∃ x : Rose α, f p = cylIn _ x}

theorem cylinderCoverCollapse_mem_rose p :
    cylinderCoverCollapse w hf p ∈ cylinderCoverRoseSet w f :=
  ⟨cylRetr _ (f p), cylinderCoverCollapse_projection w hf p⟩

/-- Every surviving genuine edge of a collapsed finite chain lies in the actual rose preimage. -/
theorem cylinderCoverCollapsedChain_support_rose c :
    ∀ e ∈ (normalizedStrictChain1 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c).support,
      e.1.1 ∈ cylinderCoverRoseSet w f ∧ e.1.2 ∈ cylinderCoverRoseSet w f := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    intro e he
    rw [map_add] at he
    rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
    · simp_all
    simp_all
  | single t n =>
    intro e he
    rw [normalizedStrictChain1_single] at he
    by_cases h : cylinderCoverCollapse w hf t.1.1 = cylinderCoverCollapse w hf t.1.2
    · simp [normalizeOrdEdge, h] at he
    · simp only [normalizeOrdEdge, dif_neg h] at he
      let r : StrictOrdEdge P := ⟨(cylinderCoverCollapse w hf t.1.1,
        cylinderCoverCollapse w hf t.1.2),
        by grind⟩
      change e ∈ (n • Finsupp.single r (1)).support at he
      have hr : e = r := by
        by_contra hn
        simp_all
      subst e
      exact ⟨cylinderCoverCollapse_mem_rose w f hf t.1.1,
        cylinderCoverCollapse_mem_rose w f hf t.1.2⟩
