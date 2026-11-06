module

public import proofs.HordijkSteelThreshold.ConnectedContourCounting
public import proofs.HordijkSteelThreshold.WordDiamondDegree

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

variable (L N : ℕ)

def wordContourGraph  : SimpleGraph (WordBasicEdge L N) where
  Adj e d := e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧
    e ≠ d ∧ wordDiamondAdjacent e d
  symm := ⟨fun _ _ ⟨he, hd, hn, v, i, j, hi, hj⟩ => ⟨hd, he, hn.symm, v, j, i, hj, hi⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem wordContourGraph_degree  (e : WordBasicEdge L N) :
    ((wordContourGraph L N).neighborFinset e).card ≤ 9 := by
  have h := mem_neighborFinset (wordContourGraph L N) e
  by_cases he : e ∈ wordBasicEdges L N
  · exact (Finset.card_le_card fun d hd => (wordDiamond_neighbor_iff e d).mpr
      ⟨((h d).mp hd).2.2.1.symm, ((h d).mp hd).2.2.2⟩).trans $ wordDiamond_neighbors_card e he
  · rw [Finset.card_eq_zero.2 $ Finset.eq_empty_of_forall_notMem fun d hd => he ((h d).mp hd).1]
    omega

theorem wordContour_crossing {L N : ℕ} (C : Finset $ WordBasicEdge L N)
    (hsub : C ⊆ wordBasicEdges L N) (r : WordBasicEdge L N)
    (hconn : ∀ d ∈ C, wordContourReach C r d)
    (S : Finset $ WordBasicEdge L N) (hs : S ⊆ C) (hr : r ∈ S) (hne : S ≠ C) :
    ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ (wordContourGraph L N).Adj u v := by
  by_contra h
  have closed : ∀ u ∈ C, ∀ v ∈ C, wordDiamondAdjacent u v → u ∈ S → v ∈ S := fun u hu v hv ha huS =>
    by_contra fun hvS => h ⟨u, huS, v, hv, hvS, hsub hu, hsub hv, by grind, ha⟩
  have := fun d hd => (eqvGen_congr (· ∈ S) (fun u v ⟨hu, hv, w, i, j, hi, hj⟩ => propext
    ⟨closed u hu v hv ⟨w, i, j, hi, hj⟩, closed v hv u hu ⟨w, j, i, hj, hi⟩⟩) $ hconn d hd).to_iff
  grind

variable (r : WordBasicEdge L N) (b : ℕ)

noncomputable def wordAnchoredContours   :=
  (wordBasicEdges L N).powerset.filter (fun C => C.card = b ∧ r ∈ C ∧
    ∀ d ∈ C, wordContourReach C r d)

/-- Literal indexed-edge contour count, uniform in the ambient word cap. -/
theorem wordAnchoredContours_card   :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1) := by
  refine (Finset.card_le_card fun C hC => ?_).trans $ (Finset.card_image_le (f := fun p => p.support.toFinset)).trans
    ((card_walks_le_degree_pow _ 9 (wordContourGraph_degree L N) (2*(b-1)) r r).trans $ by rw [pow_mul]; norm_num)
  obtain ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour _ C r hr $ wordContour_crossing C (Finset.mem_powerset.mp hpow) r hc
  exact Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr $ by omega, hp⟩


/-- Every nonempty minimal word cut containing the anchor is counted. -/
theorem wordBond_mem_anchored {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (r : WordBasicEdge L N) (hr : r ∈ wordGraphCut f) :
    wordGraphCut f ∈ wordAnchoredContours L N r (wordGraphCut f).card :=
  Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr $ Finset.filter_subset _ _, rfl, hr,
    fun d hd => wordBond_diamond_connected f hmin r d hr hd⟩

end HordijkSteelThreshold
