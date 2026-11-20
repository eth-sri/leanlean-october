module

public import RequestProject.StrictSubposetChains
public import RequestProject.NormalizedStrictBoundary
public import RequestProject.PresCylinderCoverCycles

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

def cylinderCoverRoseSet := {p | ∃ x : Rose α, f p = cylIn (aHom w) x}

theorem cylinderCoverCollapse_mem_rose (p : P) :
    cylinderCoverCollapse w hf p ∈ cylinderCoverRoseSet w f :=
  ⟨cylRetr _ (f p), cylinderCoverCollapse_projection w hf p⟩

/-- Every surviving genuine edge of a collapsed finite chain lies in the actual rose preimage. -/
theorem cylinderCoverCollapsedChain_support_rose (c : StrictOrdEdge P →₀ ℤ) :
    ∀ e ∈ (normalizedStrictChain1 _
      (cylinderCoverCollapse_monotone w hf) c).support,
      e.1.1 ∈ cylinderCoverRoseSet w f ∧ e.1.2 ∈ cylinderCoverRoseSet w f := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    intro e he
    rw [map_add] at he
    rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
    · exact hc e h
    · exact hd e h
  | single t n =>
    intro e he
    rw [normalizedStrictChain1_single] at he
    by_cases h : cylinderCoverCollapse w hf t.1.1 = cylinderCoverCollapse w hf t.1.2
    · simp_all [normalizeOrdEdge, h]
    · simp only [normalizeOrdEdge, dif_neg h] at he
      let r : StrictOrdEdge P := ⟨(cylinderCoverCollapse w hf _,
        cylinderCoverCollapse w hf _),
        lt_of_le_of_ne (cylinderCoverCollapse_monotone w hf t.2.le) h⟩
      change e ∈ (n • Finsupp.single r 1).support at he
      have hr : e = r := by
        by_contra hn
        simp_all
      grind [cylinderCoverCollapse_mem_rose]

end FiniteChains.PresModel
