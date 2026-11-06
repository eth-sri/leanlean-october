module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathHost
public import Chazelle.Core.DownPhaseDrvMBase
public import Chazelle.Existence.Rotate
public import Chazelle.Mountain.PiecesMain

/-!
# Down phase, math (H-R1, H-R2): host lists up to rotation and reversal

A list `L` of symbolic points that represents the host keys of a region `R` cyclically from the
index `i0` on (`RepPt` for `(i0 + j) mod nk` at position `j`) evaluates to the host polygon
rotated by `i0` (`poly_of_rep`, H-R1), and consecutive points satisfy `HostEdgeOK` (`edgeOK_of_rep`,
H-R2).  The driver writes the host of a clockwise `Q` in reversed order; regularity is symmetric
(`hostEdgeOK_symm`) and simplicity, the boundary and the filled region are invariant under rotation
and reversal (`polyFacts_rotate`, `polyFacts_rev`):

* `PolyFacts Q S R P`: `P` is simple, its interior is `R`, its boundary lies on `∂Q ∪ ⋃ S`, and
  every vertex of `hostPoly Q S R` is a vertex of `P`.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open DownHost

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- Polygons with the same vertices are equal. -/
theorem poly_eq_of_vtx {P P' : Polygon} (hn : P.n = P'.n)
    (hv : ∀ i, i < P.n → P.vtx i = P'.vtx i) : P = P' := by
  cases P with
  | mk l =>
    cases P' with
    | mk l' =>
      congr 1
      have hn' := hn
      refine List.ext_getElem hn' fun i h1 h2 => ?_
      have := hv i h1
      simp only [Polygon.vtx] at this
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- `HostEdgeOK` is symmetric. -/
theorem hostEdgeOK_symm {n : ℕ} {s s' : SymPt} (h : HostEdgeOK n s s') : HostEdgeOK n s' s := by
  cases s <;> cases s' <;> simp only [HostEdgeOK] at h ⊢ <;> tauto

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

/-- **H-R1 (list level)**: a list representing the host keys from index `i0` on evaluates to the
host polygon rotated by `i0`. -/
theorem poly_of_rep {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q)
    (hdh : DistinctHeights Q) {L : List SymPt} {i0 : ℕ}
    (hL : L.length = nk (interiorModel Q) S R)
    (hrep : ∀ j, j < nk (interiorModel Q) S R →
      RepPt li Q S R ((i0 + j) % nk (interiorModel Q) S R) (L.getD j (.vtx 0))) :
    (⟨L.map (SymPt.eval Q)⟩ : Polygon) = (hostPoly Q S R).rotate i0 := by
  have h3 := three_le_nk hQ hFam hne hR
  apply poly_eq_of_vtx
  · show (L.map (SymPt.eval Q)).length = ((hostPoly Q S R).rotate i0).n
    Ξ Existence.n_rotate, hostPoly_n, List.length_map, hL
  · intro j hj
    have hj' : j < nk (interiorModel Q) S R := by simpa [Polygon.n, hL] using hj
    have hjL : j < L.length := by rw [hL]; exact hj'
    have hlt : (i0 + j) % nk (interiorModel Q) S R < nk (interiorModel Q) S R :=
      Nat.mod_lt _ (⋄)
    rw [Existence.vtx_rotate _ _ (by rw [hostPoly_n]; exact hj'), hostPoly_n,
      hostPoly_vtx hlt, ← rep_eval hQ hFam hne hR hli hdh hlt (hrep j hj')]
    ϴ Polygon.vtx
    rw [List.getD_eq_getElem _ _ (by simpa using hjL), List.getElem_map,
      List.getD_eq_getElem _ _ hjL]

/-- **H-R2 (list level)**: consecutive points of a representing list satisfy `HostEdgeOK`. -/
theorem edgeOK_of_rep {li : Bool} (hdh : DistinctHeights Q) {L : List SymPt} {i0 : ℕ}
    (hL : L.length = nk (interiorModel Q) S R)
    (hrep : ∀ j, j < nk (interiorModel Q) S R →
      RepPt li Q S R ((i0 + j) % nk (interiorModel Q) S R) (L.getD j (.vtx 0))) :
    ∀ j, j < L.length →
      HostEdgeOK Q.n (L.getD j (.vtx 0)) (L.getD ((j + 1) % L.length) (.vtx 0)) := by
  have h3 := three_le_nk hQ hFam hne hR
  set N := nk (interiorModel Q) S R
  intro j hj
  rw [hL] at hj ⊢
  have hidx : (i0 + (j + 1) % N) % N = ((i0 + j) % N + 1) % N := by
    Ξ Nat.add_mod_mod, Existence.mod_add_one_mod
  have h2 := hrep ((j + 1) % N) (Nat.mod_lt _ (⋄))
  rw [hidx] at h2
  exact rep_edgeOK hQ hFam hne hR hdh (Nat.mod_lt _ (⋄)) (hrep j hj) h2

end

/-- **Regularity of a host whose points form a regular cyclic list.** -/
theorem hostRegular_of_list {n : ℕ} {H : Host}
    (h : ∀ j, j < (H.pts n).length →
      HostEdgeOK n ((H.pts n).getD j (.vtx 0))
        ((H.pts n).getD ((j + 1) % (H.pts n).length) (.vtx 0))) : HostRegular n H := h

/-- **Regularity is invariant under reversal of the point list.** -/
theorem regular_reverse {n : ℕ} {L : List SymPt}
    (h : ∀ j, j < L.length → HostEdgeOK n (L.getD j (.vtx 0)) (L.getD ((j + 1) % L.length) (.vtx 0))) :
    ∀ j, j < L.reverse.length →
      HostEdgeOK n (L.reverse.getD j (.vtx 0)) (L.reverse.getD ((j + 1) % L.reverse.length) (.vtx 0)) := by
  intro j hj
  rw [List.length_reverse] at hj ⊢
  set m := L.length
  have hrev : ∀ k, k < m → L.reverse.getD k (.vtx 0) = L.getD (m - 1 - k) (.vtx 0) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
  have hj1 : (j + 1) % m < m := Nat.mod_lt _ (by omega)
  rw [hrev j hj, hrev _ hj1]
  -- the pair is the reversed pair at index `m - 1 - (j + 1) % m`
  set k := m - 1 - (j + 1) % m with hk
  have hkm : k < m := by omega
  have hk1 : (k + 1) % m = m - 1 - j := by
    by_cases h1 : j + 1 < m
    · rw [Nat.mod_eq_of_lt h1] at hk
      rw [hk, Nat.mod_eq_of_lt (by omega)]; omega
    · have : j + 1 = m := by omega
      rw [this, Nat.mod_self] at hk
      rw [hk, show m - 1 - 0 + 1 = m by omega, Nat.mod_self]; omega
  have := h k hkm
  rw [hk1] at this
  exact hostEdgeOK_symm this

/-! ## Geometric facts of rotated and reversed host polygons -/

/-- The facts the driver consumes about the polygon of its host description. -/
def PolyFacts (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (P : Polygon) : Prop :=
  P.Simple ∧ P.filled \ P.boundary = R ∧ P.boundary ⊆ Q.boundary ∪ ⋃₀ S ∧
    ∀ j, j < (hostPoly Q S R).n → ∃ j', j' < P.n ∧ P.vtx j' = (hostPoly Q S R).vtx j

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

/-- The facts for a rotation of the host polygon. -/
theorem polyFacts_rotate (i0 : ℕ) : PolyFacts Q S R ((hostPoly Q S R).rotate i0) := by
  have hs := hostPts_simple hQ hFam hne hR
  have hint := DownDrv.region_eq_intHost hQ hFam hne hR
  have hbd := DownDrv.hostPoly_bd_sub hQ hFam hne hR
  have h3 := three_le_nk hQ hFam hne hR
  refine ⟨Existence.simple_rotate _ _ hs, ?_, ?_, ?_⟩
  · rw [Existence.filled_rotate, Existence.boundary_rotate]; exact hint.symm
  · rw [Existence.boundary_rotate]; exact hbd
  · intro j hj
    have hn : 0 < (hostPoly Q S R).n := ⋄
    obtain ⟨i, hi, hij⟩ := Existence.exists_rot_index hn i0 j hj
    exact ⟨i, by rw [Existence.n_rotate]; exact hi, Ρ Existence.vtx_rotate _ _ hi, hij⟩

/-- The facts for a reversal of a rotation of the host polygon. -/
theorem polyFacts_rev (i0 : ℕ) {P : Polygon} (hn : P.n = ((hostPoly Q S R).rotate i0).n)
    (hv : ∀ k, k < ((hostPoly Q S R).rotate i0).n →
      P.vtx k = ((hostPoly Q S R).rotate i0).vtx (((hostPoly Q S R).rotate i0).n - 1 - k)) :
    PolyFacts Q S R P := by
  obtain ⟨hs, hint, hbd, hvx⟩ := polyFacts_rotate hQ hFam hne hR i0
  have hbd' := Mountain.rev_boundary hn hv
  refine ⟨Mountain.rev_simple hn hv hs, ?_, ?_, ?_⟩
  · rw [Mountain.rev_filled hn hv, hbd']; exact hint
  · rw [hbd']; exact hbd
  · intro j hj
    obtain ⟨j', hj', e⟩ := hvx j hj
    set m := ((hostPoly Q S R).rotate i0).n
    refine ⟨m - 1 - j', by rw [hn]; omega, ?_⟩
    rw [hv _ (⋄), show m - 1 - (m - 1 - j') = j' by omega]
    exact e

end

end

end DownMath

end Chazelle.Core
