module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBShot
public import Chazelle.Core.DownPhaseDrvMBase
public import Chazelle.Core.DownPhaseDrvOrient
public import Chazelle.Core.DownPhaseMathWalkAll
public import Chazelle.Core.DownPhaseMathHostList

/-!
# Down-phase base (D9): the polygon in which a region shoots

For a region `R` of the interior family `S`, the base case shoots inside a simple polygon `W₀`
with the interior on its left, whose interior is `R` and whose boundary lies on `∂Q` and on the
chords of `S` (`RegOK`), and which has every vertex of `Q` from which a missing vertex chord of
`R` starts (completeness).

* `RegOK.sound`: a shot inside `W₀` from a vertex of `W₀` that is a vertex `i` of `Q` is the vertex
  chord of `Q` at `i`, not in `S`, with its domain part in `R` (`DownDrv.chord_of_host`);
* `regOK_host`: for region `r` of `N = buildNF I Q L E` (`K > 0`), the walk-order points of the
  driver's host `regHost` (`DownMath.walk_rep`) form the rotated host polygon (`poly_of_rep`), which
  is `RegOK` (`polyFacts_rotate`, `hostPoly_orient`, completeness `DownDrv.missing_found`);
* `regOK_empty`: for `K = 0` the interior walk of `Q` itself is `RegOK` for the empty family.

`wlist li pts`: the walk-order list of the points `pts` of a host stored in increasing index of
`Q` (reversed when `¬ LeftInside Q`).
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt regionsIn freeIn)
open Chazelle.Visibility (DirInterior rayPt chordEnd chordSet chordParam chords hseg)
open DrvR (ivB qE walkItems regHost)
open BuildNF (buildNF)

/-! ## The shooting polygon of a region -/

/-- **The shooting polygon** `W₀` of the region `R` of `S`: simple, interior on its left, interior
`R`, boundary on `∂Q ∪ ⋃ S`, and complete for the missing vertex chords of `R`. -/
structure RegOK (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (W₀ : Polygon) : Prop where
  simple : W₀.Simple
  orient : Mountain.orient W₀ = 1
  int : W₀.filled \ W₀.boundary = R
  bd : W₀.boundary ⊆ Q.boundary ∪ ⋃₀ S
  reg : R ∈ (interiorModel Q).regions S
  complete : ∀ i σ, i < Q.n → (σ = 1 ∨ σ = -1) → DirInterior Q i σ → chordSet Q i σ ∉ S →
    chordSet Q i σ ∩ (interiorModel Q).D ⊆ R →
      ∃ k, k < W₀.n ∧ W₀.vtx k = Q.vtx i ∧ DirInterior W₀ k σ

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {W₀ : Polygon}

/-- **Soundness of a shot in the shooting polygon.** -/
theorem RegOK.sound (h : RegOK Q S R W₀) (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) {i k : ℕ} (hi : i < Q.n)
    (hv : W₀.vtx k = Q.vtx i) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior W₀ k σ) :
    DirInterior Q i σ ∧ chordSet Q i σ = chordSet W₀ k σ ∧ chordSet Q i σ ∈ chords Q ∧
      chordSet Q i σ ∉ S ∧ chordSet Q i σ ∩ (interiorModel Q).D ⊆ R :=
  DownDrv.chord_of_host hQ hFam h.reg h.simple h.int h.bd hi hv hσ hdir

/-! ## Rotations keep the orientation -/

/-- A rotation of a simple polygon has its orientation. -/
theorem orient_rotate {P : Polygon} (hP : P.Simple) (s : ℕ) :
    Mountain.orient (P.rotate s) = Mountain.orient P := by
  have hn := Chazelle.Jordan.simple_three_le hP
  have hs := Existence.simple_rotate P s hP
  have h0 : 0 < (P.rotate s).n := by rw [Existence.n_rotate]; omega
  have h1 : (0 + 1) % (P.rotate s).n < P.n := by rw [Existence.n_rotate]; exact Nat.mod_lt _ (⋄)
  refine Mountain.orient_eq_of_filled_subset hP hs (i := s % P.n) (j := 0)
    (Nat.mod_lt _ (⋄)) h0 ?_ ?_ (Ρ Existence.filled_rotate)
  · Ξ Existence.vtx_rotate _ _ (⋄), Nat.add_zero
  · rw [Existence.vtx_rotate_succ _ _ (⋄)]; simp

/-! ## The walk-order list of a host -/

/-- The walk-order list of host points stored in increasing index of `Q`. -/
def wlist (li : Bool) (pts : List SymPt) : List SymPt := if li then pts else pts.reverse

theorem wlist_length (li : Bool) (pts : List SymPt) : (wlist li pts).length = pts.length := by
  unfold wlist; split_ifs <;> simp

/-- The point of walk-order index `k` is the stored point `k` (or `N - 1 - k` if reversed). -/
theorem wlist_getD (li : Bool) {pts : List SymPt} {k : ℕ} (hk : k < pts.length) :
    (wlist li pts).getD k (.vtx 0) = pts.getD (if li then k else pts.length - 1 - k) (.vtx 0) := by
  unfold wlist
  cases li
  · ϴ Bool.false_eq_true, ite_false
    Ξ List.getD_eq_getElem?_getD, List.getElem?_reverse hk, List.getD_eq_getElem?_getD
  · rfl

/-- The polygon of a list of symbolic points. -/
noncomputable def polyOf (Q : Polygon) (l : List SymPt) : Polygon := ⟨l.map (SymPt.eval Q)⟩

theorem polyOf_n (Q : Polygon) (l : List SymPt) : (polyOf Q l).n = l.length := by
  Θ polyOf, Polygon.n

theorem polyOf_vtx (Q : Polygon) {l : List SymPt} {k : ℕ} (hk : k < l.length) :
    (polyOf Q l).vtx k = (l.getD k (.vtx 0)).eval Q := by
  simp only [polyOf, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]

/-! ## The host of a region (`K > 0`) -/

/-- **The driver's host of a region gives a shooting polygon** (walk order). -/
theorem regOK_host {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {r : ℕ}
    (X : DownMath.RegCtx Q L E reg r) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r)
      (polyOf Q (wlist li ((regHost li Q.n (buildNF (interiorModel Q) Q L E) r).pts Q.n))) := by
  set N := buildNF (interiorModel Q) Q L E with hNdef
  set S := N.F (interiorModel Q) Q with hS
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, hwf⟩ := DownMath.walk_rep X hli
  set WP := (walkItems li Q.n N r).flatMap (DownMath.wpts li Q.n) with hWP
  have hQ := X.hQ
  have hN : IsNF (interiorModel Q) Q N := DownMath.isNF_build hQ X.hL X.hperm X.hsort
  have hFam : (interiorModel Q).ChordFamily Q S := hN.1
  have hnc : N.nChords = L.length := DownMath.nChords_build hQ X.hL X.hperm X.hsort
  have hne : S.Nonempty :=
    ⟨_, (DownMath.chordPos_attach hN (show 0 < N.nChords by rw [hnc]; exact X.hK) (Or.inl rfl)).1⟩
  have hR : reg r ∈ (interiorModel Q).regions S := X.hregs.1.1 r X.hr
  set K := DownHost.nk (interiorModel Q) S (reg r) with hKdef
  have hrep' : ∀ j, j < K → DownMath.RepPt li Q S (reg r) ((i0 + j) % K) (WP.getD j (.vtx 0)) :=
    fun j hj => hrep j (by rw [hlen]; exact hj)
  have hrot : (⟨WP.map (SymPt.eval Q)⟩ : Polygon) = (DownHost.hostPoly Q S (reg r)).rotate i0 :=
    DownMath.poly_of_rep hQ hFam hne hR hli X.hdh hlen hrep'
  have hwl : wlist li ((regHost li Q.n N r).pts Q.n) = WP := by
    Ξ DownMath.regHost_pts
    unfold wlist
    cases li <;> simp [hWP]
  have hP : polyOf Q (wlist li ((regHost li Q.n N r).pts Q.n)) =
      (DownHost.hostPoly Q S (reg r)).rotate i0 := by
    rw [hwl]; exact hrot
  Ξ hP
  obtain ⟨hs, hint, hbd, -⟩ := DownMath.polyFacts_rotate hQ hFam hne hR i0
  have hHs : (DownHost.hostPoly Q S (reg r)).Simple := DownHost.hostPts_simple hQ hFam hne hR
  refine ⟨hs, ?_, hint, hbd, hR, ?_⟩
  · rw [orient_rotate hHs]; exact DownDrv.hostPoly_orient hQ hFam hne hR
  · intro i σ hi hσ hdir hcS hcR
    have hc : chordSet Q i σ ∈ chords Q := ⟨i, σ, hi, hσ, hdir, rfl⟩
    obtain ⟨R', hR', i', σ', hi', hσ', hceq, hdir', hcR', j, hj, hjv, hdirj⟩ :=
      DownDrv.missing_found hQ hFam hne hc hcS
    obtain ⟨-, -, -, hnon⟩ := DownDrv.full_in_region hQ hFam hc hcS
    obtain ⟨rfl, rfl⟩ := DownDrv.chordSet_inj hQ X.hdh hi hi' hσ hσ' hdir hdir' hceq
    have hRR : reg r = R' := by
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint hR hR' with h | h
      · exact h
      · obtain ⟨z, hz⟩ := hnon
        exact absurd (h.le_bot ⟨hcR hz, hcR' hz⟩) (✓)
    subst hRR
    have hn0 : 0 < (DownHost.hostPoly Q S (reg r)).n := ⋄
    obtain ⟨k, hk, hkj⟩ := Existence.exists_rot_index hn0 i0 j hj
    refine ⟨k, by rw [Existence.n_rotate]; exact hk, ?_, ?_⟩
    · Ξ Existence.vtx_rotate _ _ hk, hkj, hjv
    · unfold DirInterior
      Ξ Existence.vtx_rotate _ _ hk, hkj, Existence.filled_rotate, Existence.boundary_rotate
      exact hdirj

/-! ## The whole walk (`K = 0`) -/

/-- The interior of a simple polygon is the only region of the empty family. -/
theorem region_empty (hQ : Q.Simple) :
    (interiorModel Q).D ∈ (interiorModel Q).regions (∅ : Set (Set Point)) := by
  have hM := walkAx_interiorModel hQ
  obtain ⟨z, hz⟩ := hM.nonempty
  have hfree : freeIn (interiorModel Q).D (∅ : Set (Set Point)) = (interiorModel Q).D := by
    ext x; Θ freeIn
  refine ⟨z, by rw [hfree]; exact hz, ?_⟩
  Ξ hfree
  exact (hM.preconn.connectedComponentIn hz).symm

/-- **The interior walk is the shooting polygon of the empty family.** -/
theorem regOK_empty (hQ : Q.Simple) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ∅ (interiorModel Q).D (interiorWalk Q) := by
  obtain ⟨hs, hb, hf, ho⟩ := FactsInterior.interiorWalk_spec hQ
  refine ⟨hs, ho, by rw [hb, hf]; rfl, by rw [hb]; exact subset_union_left, region_empty hQ, ?_⟩
  intro i σ hi hσ hdir _ _
  have hk := DownMath.ivB_lt li hi
  refine ⟨ivB li Q.n i, by rw [DownMath.walk_n]; exact hk, ?_, ?_⟩
  · Ξ DownMath.walk_vtx hli hk, ivB_ivB li hi
  · unfold DirInterior
    Ξ DownMath.walk_vtx hli hk, ivB_ivB li hi, hf, hb
    exact hdir

/-- The walk-order list of the host `[.run 0 (n - 1)]` is the interior walk. -/
theorem polyOf_wlist_run (hQ : Q.Simple) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    polyOf Q (wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)])) = interiorWalk Q := by
  have hn := Chazelle.Jordan.simple_three_le hQ
  have hpts : Host.pts Q.n [HostItem.run 0 (Q.n - 1)] =
      (List.range Q.n).map fun k => SymPt.vtx k := by
    ϴ Host.pts, List.flatMap_cons, List.flatMap_nil, List.append_nil, HostItem.pts
    Ξ Nat.sub_add_cancel (by omega : 1 ≤ Q.n)
    apply List.map_congr_left
    intro k hk
    Ξ' List.mem_range at hk
    Ξ Nat.zero_add, Nat.mod_eq_of_lt hk
  have hlen : (wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)])).length = Q.n := by
    Ξ wlist_length, hpts, List.length_map, List.length_range
  apply DownMath.poly_eq_of_vtx
  · Ξ polyOf_n, hlen, DownMath.walk_n
  · intro k hk
    Ξ' polyOf_n, hlen at hk
    rw [polyOf_vtx Q (by rw [hlen]; exact hk), DownMath.walk_vtx hli hk,
      wlist_getD li (by rw [hpts, List.length_map, List.length_range]; exact hk), hpts]
    ϴ List.length_map, List.length_range
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by split_ifs <;> omega)]
    ϴ Option.map_some, Option.getD_some, SymPt.eval
    unfold ivB; split_ifs <;> rfl

end

end DrvB

end Chazelle.Core
