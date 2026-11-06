module

public import PottsDiscontinuity.TorusLoops.RectangleCrossings

/-!
# Crossing components of the cut rectangle

These components are defined from the cut graph itself, so their count is
unchanged by changing any edge state on either deleted seam. This is the event
needed for the finite-energy comparison.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
/-- Distinct components of the cut rectangle that connect its left and right
vertex boundaries. -/
noncomputable def rectangleCrossingComponents  : Finset (rectangleOpenGraph hN hM A).ConnectedComponent := by
  classical
  letI : Fintype (rectangleOpenGraph hN hM A).ConnectedComponent := Fintype.ofFinite _
  exact Finset.univ.filter fun c =>
    ∃ u v, u.val.1.val = 0 ∧ v.val.1.val + 1 = N ∧
      (rectangleOpenGraph hN hM A).connectedComponentMk u = c ∧
      (rectangleOpenGraph hN hM A).Reachable u v

/-- Closing or opening one indexed seam edge does not change the cut graph. -/
theorem rectangleOpenGraph_toggleEdge_seam (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleOpenGraph hN hM (toggleEdge A v) = rectangleOpenGraph hN hM A := by
  ext u w
  rw [rectangleOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he, hx, hy, hp⟩, hne⟩
    have hev : e ≠ v := by
      grind
    have hA : A e = true := by
      rw [toggleEdge_away A hev] at he
      omega
    exact ⟨⟨e, hA, hx, hy, hp⟩, hne⟩
  · rintro ⟨⟨e, he, hx, hy, hp⟩, hne⟩
    have hev : e ≠ v := by
      grind
    have htoggle : toggleEdge A v e = A e := by
      rw [toggleEdge_away A hev]
    grind

/-- The cut graphs before and after a seam toggle are canonically isomorphic. -/
def rectangleOpenGraph_toggleEdge_iso (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleOpenGraph hN hM (toggleEdge A v) ≃g rectangleOpenGraph hN hM A where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    simp_all [rectangleOpenGraph_toggleEdge_seam]

/-- The number of cut-rectangle crossing components is seam-invariant. -/
theorem rectangleCrossingComponents_card_toggleEdge_seam
    (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    (rectangleCrossingComponents hN hM (toggleEdge A v)).card =
      (rectangleCrossingComponents hN hM A).card := by
  classical
  let φ := rectangleOpenGraph_toggleEdge_iso hN hM A v hseam
  let e := φ.connectedComponentEquiv
  let : Fintype (rectangleOpenGraph hN hM (toggleEdge A v)).ConnectedComponent :=
    Fintype.ofFinite _
  let : Fintype (rectangleOpenGraph hN hM A).ConnectedComponent := Fintype.ofFinite _
  have hmap :
      (rectangleCrossingComponents hN hM (toggleEdge A v)).map e.toEmbedding =
        rectangleCrossingComponents hN hM A := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_map.mp hc with ⟨d, hd, hdc⟩
      rcases Finset.mem_filter.mp hd with ⟨_, u, w, hu, hw, hdu, hreach⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, w, hu, hw, ?_, ?_⟩
      · aesop
      grind [rectangleOpenGraph, rectangleOpenGraph_toggleEdge_seam]
    · intro hc
      rcases Finset.mem_filter.mp hc with ⟨_, u, w, hu, hw, hcu, hreach⟩
      let d := e.symm c
      have hreach' :
          (rectangleOpenGraph hN hM (toggleEdge A v)).Reachable u w :=
        by
          simp_all [rectangleOpenGraph_toggleEdge_seam]
      have hdu :
          (rectangleOpenGraph hN hM (toggleEdge A v)).connectedComponentMk u = d := by
        aesop
      refine Finset.mem_map.mpr ⟨d,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, w, hu, hw, hdu, hreach'⟩, ?_⟩
      aesop
  have hcard := congrArg Finset.card hmap
  simpa using hcard
end

section
variable (hN : Even N) (hM : Even M) (k : ℕ)
/-- The event that at least `k` distinct cut-rectangle components cross
horizontally. -/
def hasAtLeastRectangleCrossings  :
    Set (RCConfig N M) :=
  {A | k ≤ (rectangleCrossingComponents hN hM A).card}

/-- The crossing-count event is invariant under toggling any seam edge. -/
theorem hasAtLeastRectangleCrossings_toggleEdge_seam
    (A : RCConfig N M)
    (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    A ∈ hasAtLeastRectangleCrossings hN hM k ↔
      toggleEdge A v ∈ hasAtLeastRectangleCrossings hN hM k := by
  simp_all [hasAtLeastRectangleCrossings, rectangleCrossingComponents_card_toggleEdge_seam]
end

end PottsDiscontinuity.TorusLoops
