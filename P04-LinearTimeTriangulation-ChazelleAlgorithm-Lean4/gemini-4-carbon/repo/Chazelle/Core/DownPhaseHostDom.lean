module

public import Chazelle.Core.DownPhaseRegionBox

/-!
# WP-M (X, part 10): the region lies in the domain of its host chain

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q` and a gap `g` of its
host keys, the host chain `C = hostChain Q S R g` has `R ⊆ C.dom` (`region_sub_dom`):
* `R` lies in the box of `C`, because it lies within the coordinate bound of its host points
  (`region_abs_le`);
* `R` misses the chain: every chain edge is a piece of the walk or a chord of `S`
  (`hostEdge_sub`);
* `R` misses the slit: `R` lies below the top vertex (`region_below`), and the only slit point at
  that height is the top vertex.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt freeIn regionsIn)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (coordBound)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The host edges avoid the region**: the segment between consecutive host points is a piece
of the walk or a chord of `S`. -/
theorem hostEdge_not_mem (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    {i : ℕ} (hi : i < nk (interiorModel Q) S R) {z : Point}
    (hz : z ∈ Chazelle.segment (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i))
      (hostPt (interiorModel Q).W
        (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)))) :
    z ∉ R := by
  set M := interiorModel Q
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ nk M S R := three_le_nk hQ hFam hne hR
  have hN2 : 2 ≤ nk M S R := le_trans (by norm_num) h3
  intro hzR
  have hzfree := Chazelle.Chain.regionsIn_subset hR hzR
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA, hB,
    ha, hb, hAB⟩
  · have hsi : (i + 1) % nk M S R < nk M S R := Nat.mod_lt _ (by omega)
    have hb1 := hostKeys_bounds (hk_mem hM hF hfin hi)
    have hb2 := hostKeys_bounds (hk_mem hM hF hfin hsi)
    have hnv : ∀ k : ℕ, k < M.W.n →
        ¬ sideInArc (hk M S R i) (hk M S R ((i + 1) % nk M S R)) k := by
      intro k hk hkin
      exact hk_gap hM hF hfin hN2 hi
        (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k (Nat.cast_nonneg k) (by exact_mod_cast hk) hkin⟩)
        hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      (hk_succ_ne hM hF hfin hN2 hi) hnv z hz
    exact hM.trace q hq s hs0 hs1.le (hzq ▸ hzfree.1)
  · have hPa : hostPt M.W (hk M S R i) = sidePt M.W p t := by
      rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
    have hPb : hostPt M.W (hk M S R ((i + 1) % nk M S R)) = sidePt M.W p' t' := by
      rw [hb, hostPt_eq M.W hB.2.1 hB.2.2.1]
    obtain ⟨hcab, -⟩ := hM.attach_seg (hF hc) hA hB hAB
    rw [hPa, hPb, ← hcab] at hz
    exact hzfree.2 ⟨c, hc, hz⟩

variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The region lies in the domain of the host chain.** -/
theorem region_sub_dom (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ (hostChain Q S R g h3).dom := by
  set M := interiorModel Q
  set C := hostChain Q S R g h3
  set N := nk M S R
  have hN : 0 < N := by omega
  have hCn : C.P.n = N := hostPoly_n
  -- every host point is a chain vertex
  have hvert : ∀ i, i < N → ∃ k, k ≤ C.m ∧ C.vertex k = hostPt M.W (hk M S R i) := by
    intro i hi
    refine ⟨(i + N - (g + 1) % N) % N, by
      have := Nat.mod_lt (i + N - (g + 1) % N) hN; show _ ≤ N - 1; omega, ?_⟩
    rw [hostChain_vertex, add_steps_mod (Nat.mod_lt _ hN) hi]
  -- the box
  have hbox : ∀ z ∈ R, z ∈ Chazelle.Chain.box C.radius := by
    intro z hz
    have hB : ∀ i, i < N → |(hostPt M.W (hk M S R i)).1| ≤ coordBound C.P ∧
        |(hostPt M.W (hk M S R i)).2| ≤ coordBound C.P := by
      intro i hi
      obtain ⟨k, hk, e⟩ := hvert i hi
      rw [← e]
      exact C.abs_le_coordBound_of_mem_set (C.vertex_mem_set hk)
    have := region_abs_le hQ hFam hne hR hB z hz
    exact this
  -- the chain
  have hset : ∀ z ∈ R, z ∉ C.set := by
    intro z hz ⟨k, hk, hzk⟩
    rw [C.chainEdge_eq, hostChain_vertex, hostChain_vertex] at hzk
    set i := ((g + 1) % N + k) % N
    have hi : i < N := Nat.mod_lt _ hN
    have e : ((g + 1) % N + (k + 1)) % N = (i + 1) % N := by
      rw [show (g + 1) % N + (k + 1) = (g + 1) % N + k + 1 by ring, ← Nat.mod_add_mod]
    rw [e] at hzk
    exact hostEdge_not_mem hQ hFam hne hR hi hzk hz
  -- the slit
  have htop : ∀ z ∈ R, z.2 ≤ C.top.2 := by
    refine region_below hQ hFam hne hR (fun i hi => ?_)
    obtain ⟨k, hk, e⟩ := hvert i hi
    rw [← e]; exact C.vertex_snd_le_top hk
  intro z hz
  refine (C.mem_dom_iff).2 ⟨hbox z hz, hset z hz, fun hs => ?_⟩
  obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hs
  have h3' := htop z hz
  have hzt : z = C.top := Prod.ext h1 (le_antisymm h3' h2)
  exact hset z hz (hzt ▸ C.top_mem_set)

/-- **Every host point is a chain vertex.** -/
theorem host_vertex (_h3' : 3 ≤ nk (interiorModel Q) S R) {i : ℕ}
    (hi : i < nk (interiorModel Q) S R) :
    ∃ k, k ≤ (hostChain Q S R g h3).m ∧
      (hostChain Q S R g h3).vertex k = hostPt (interiorModel Q).W (hk (interiorModel Q) S R i) := by
  set N := nk (interiorModel Q) S R
  have hN : 0 < N := by omega
  refine ⟨(i + N - (g + 1) % N) % N, by
    have := Nat.mod_lt (i + N - (g + 1) % N) hN; show _ ≤ N - 1; omega, ?_⟩
  rw [hostChain_vertex, add_steps_mod (Nat.mod_lt _ hN) hi]

/-- **The region lies below the top of its host chain.** -/
theorem region_below_top (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    ∀ z ∈ R, z.2 ≤ (hostChain Q S R g h3).top.2 := by
  refine region_below hQ hFam hne hR (fun i hi => ?_)
  obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3 hi
  rw [← e]; exact (hostChain Q S R g h3).vertex_snd_le_top hk

end

end DownHost

end Chazelle.Core
