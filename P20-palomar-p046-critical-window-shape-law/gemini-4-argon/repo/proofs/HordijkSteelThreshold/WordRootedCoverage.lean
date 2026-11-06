module

public import proofs.HordijkSteelThreshold.WordContourMarginals

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer

/-- Project an actual molecule to the finite graph, contracting all food words. -/
noncomputable def molecularWordVertex (L N : ℕ) (s : List Bool) : BoundedFoodWord L N :=
  if h : L < s.length ∧ s.length ≤ N then ⟨s, Or.inr h⟩ else boundedFoodRoot L N

noncomputable def wordEffectiveEdges {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (WordBasicEdge L N) :=
  (wordBasicEdges L N).filter (fun e => ∃ j : Fin w,
    ∀ a ∈ wordDetourSourceReactions hL (e,j), ω a)

theorem outside_moleculeContourBad_connected {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s t : List Bool)
    (hs : s ∈ actualBinaryWords N) (ht : t ∈ actualBinaryWords N)
    (hsg : ¬ moleculeContourBad hL s ω) (htg : ¬ moleculeContourBad hL t ω) :
    indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
      (molecularWordVertex L N s) (molecularWordVertex L N t) := by
  by_contra hn
  obtain ⟨f, hneq, hcut, hnonempty, hmin⟩ := wordGraph_disabled_bond L N
    (wordEffectiveEdges hL ω) (molecularWordVertex L N s) (molecularWordVertex L N t) hn
  have hlbl (u : List Bool) : f (molecularWordVertex L N u) = boundedWordLabel f u := by
    by_cases hu : u = []
    · subst u; simp [molecularWordVertex, boundedWordLabel, boundedFoodRoot]
    · by_cases h : L < u.length ∧ u.length ≤ N <;> simp [molecularWordVertex, boundedWordLabel, hu, h]
  rw [hlbl s, hlbl t] at hneq
  have hfailed : contourDetoursFailed hL (wordGraphCut f) (fun r ω => ω r) ω := fun d hd hopen =>
    let ⟨hb, hn⟩ := Finset.mem_sdiff.mp (hcut (Finset.mem_product.mp hd).1)
    hn (Finset.mem_filter.mpr ⟨hb, d.2, hopen⟩)
  have hcomp (c d : Bool) (hcd : c ≠ d) : actualBinaryWords N \ wordMolecularSide f c = wordMolecularSide f d := by
    ext u; cases c <;> cases d <;> cases hu : boundedWordLabel f u <;> simp_all [wordMolecularSide]
  have hnotS : ¬ (wordMolecularSide f (boundedWordLabel f s)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f s)).card := fun hm =>
    hsg (wordBond_smaller_side_bad hL f hmin hnonempty _ hm s (Finset.mem_filter.mpr ⟨hs, rfl⟩) ω hfailed)
  have hnotT : ¬ (wordMolecularSide f (boundedWordLabel f t)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f t)).card := fun hm =>
    htg (wordBond_smaller_side_bad hL f hmin hnonempty _ hm t (Finset.mem_filter.mpr ⟨ht, rfl⟩) ω hfailed)
  rw [hcomp _ _ hneq] at hnotS
  rw [hcomp _ _ hneq.symm] at hnotT
  omega

end HordijkSteelThreshold
