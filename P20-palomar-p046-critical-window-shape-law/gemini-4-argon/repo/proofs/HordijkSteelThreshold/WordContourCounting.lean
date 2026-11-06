module

public import proofs.HordijkSteelThreshold.ConnectedContourCounting
public import proofs.HordijkSteelThreshold.WordDiamondDegree

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

def wordContourGraph (L N : ℕ) : SimpleGraph (WordBasicEdge L N) where
  Adj e d := e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧
    e ≠ d ∧ wordDiamondAdjacent e d
  symm := ⟨fun _ _ ⟨he, hd, hn, v, i, j, hi, hj⟩ => ⟨hd, he, hn.symm, v, j, i, hj, hi⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem wordContour_crossing {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (r : WordBasicEdge L N)
    (hconn : ∀ d ∈ C, wordContourReach C r d)
    (S : Finset (WordBasicEdge L N)) (hs : S ⊆ C) (hr : r ∈ S) (hne : S ≠ C) :
    ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ (wordContourGraph L N).Adj u v := by
  by_contra h
  have closed (u v) (hu : u ∈ C) (hv : v ∈ C) (ha : wordDiamondAdjacent u v) (huS : u ∈ S) : v ∈ S := by
    by_contra hvS
    exact h ⟨u, huS, v, hv, hvS, hsub hu, hsub hv, fun he => hvS (he ▸ huS), ha⟩
  have inv (u v) (hp : wordContourReach C u v) : u ∈ S ↔ v ∈ S := by
    induction hp with
    | rel u v hrel =>
      obtain ⟨hu, hv, w, i, j, hi, hj⟩ := hrel
      exact ⟨closed u v hu hv ⟨w, i, j, hi, hj⟩, closed v u hv hu ⟨w, j, i, hj, hi⟩⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact hne (Finset.Subset.antisymm hs fun d hd => (inv r d (hconn d hd)).mp hr)

noncomputable def wordAnchoredContours (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :=
  (wordBasicEdges L N).powerset.filter (fun C => C.card = b ∧ r ∈ C ∧
    ∀ d ∈ C, wordContourReach C r d)

theorem wordAnchoredContours_card (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1) := by
  simpa [pow_mul] using card_connected_contours_le (wordContourGraph L N) 9 b
    (fun e => by
      by_cases he : e ∈ wordBasicEdges L N
      · refine (Finset.card_le_card fun d hd => ?_).trans (wordDiamond_neighbors_card e he)
        obtain ⟨_, _, hn, ha⟩ := (mem_neighborFinset _ _ _).mp hd
        exact (wordDiamond_neighbor_iff e d).mpr ⟨hn.symm, ha⟩
      · rw [Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun d hd =>
          he ((mem_neighborFinset (wordContourGraph L N) e d).mp hd).1)]; omega)
    r (wordAnchoredContours L N r b) fun C hC =>
      let ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
      ⟨hb, hr, wordContour_crossing C (Finset.mem_powerset.mp hpow) r hc⟩

theorem wordBond_mem_anchored {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (r : WordBasicEdge L N) (hr : r ∈ wordGraphCut f) :
    wordGraphCut f ∈ wordAnchoredContours L N r (wordGraphCut f).card :=
  Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    rfl, hr, fun d hd => wordBond_diamond_connected f hmin r d hr hd⟩

end HordijkSteelThreshold
