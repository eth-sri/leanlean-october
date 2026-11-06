module

public import proofs.HordijkSteelThreshold.WordContourMarginals

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer

/-- Project an actual molecule to the finite graph, contracting all food words. -/
noncomputable def molecularWordVertex (L N : ℕ) (s : List Bool) : BoundedFoodWord L N :=
  if h : L < s.length ∧ s.length ≤ N then ⟨s, Or.inr h⟩ else boundedFoodRoot L N

variable {L N : ℕ} (f : BoundedFoodWord L N → Bool)

theorem molecularWordVertex_label
    (s : List Bool) : f (molecularWordVertex L N s) = boundedWordLabel f s := by
  by_cases hs : s = []
  · aesop
  · by_cases h : L < s.length ∧ s.length ≤ N
    · simp [molecularWordVertex, boundedWordLabel, hs, h]
    · simp [molecularWordVertex, boundedWordLabel, hs, h]

noncomputable def wordEffectiveEdges {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (WordBasicEdge L N) :=
  (wordBasicEdges L N).filter (fun e => ∃ j : Fin w,
    ∀ a ∈ wordDetourSourceReactions hL (e,j), ω a)

theorem wordMolecularSide_complement_of_ne  (c d : Bool) (hcd : c ≠ d) :
    actualBinaryWords N \ wordMolecularSide f c = wordMolecularSide f d := by
  ext s
  cases c <;> cases d <;> cases hs : boundedWordLabel f s <;>
    simp_all [wordMolecularSide]

end HordijkSteelThreshold
