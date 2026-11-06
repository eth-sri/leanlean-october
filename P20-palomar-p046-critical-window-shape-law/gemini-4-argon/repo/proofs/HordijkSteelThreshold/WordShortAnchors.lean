module

public import proofs.HordijkSteelThreshold.WordMolecularCounts
public import proofs.HordijkSteelThreshold.WordLongCoreAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- A cut side counted in actual molecules, including each food word separately. -/
noncomputable def wordMolecularSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) (c : Bool) :=
  (actualBinaryWords N).filter (fun s => boundedWordLabel f s = c)

theorem wordShortAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card)
    (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
  let M := e.1.val.length + 4 * (wordGraphCut f).card
  have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
  have hcut (d) (hd : d ∈ wordGraphCut f) : d.1.val.length ≤ M := by
    obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
    have := endWord_walk_length_bound p; dsimp [M]; omega
  have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
  have hLM : L < M := e.1.2.elim (fun h => (hn (Subtype.ext h)).elim) (by dsimp [M]; omega)
  have hsN := ((mem_actualBinaryWords s N).mp (Finset.mem_filter.mp hs).1).2
  have hsM : s.length ≤ M := by
    by_cases hMN : M < N
    · refine (molecular_minor_side_below_band N M hMN (wordMolecularSide f c)
        (Finset.filter_subset _ _) hminor (fun u hu v hv hMu hMv => ?_) s hs).le
      have heq := highBand_label_constant (boundedWordLabel f) M N hMN
        (wordCut_above_boundary_parents f hLM hcut) u v
        ⟨hMu, ((mem_actualBinaryWords u N).mp hu).2⟩ ⟨hMv, ((mem_actualBinaryWords v N).mp hv).2⟩
      simp [wordMolecularSide, hu, hv, heq]
    · omega
  obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val [] ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
  simp only [List.length_nil, mul_zero, add_zero] at hp
  exact ⟨p, by dsimp [M] at hsM; omega⟩

end HordijkSteelThreshold
