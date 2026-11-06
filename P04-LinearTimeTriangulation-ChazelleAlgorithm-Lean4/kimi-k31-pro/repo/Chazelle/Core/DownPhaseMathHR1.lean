module

public import Chazelle.Core.DownPhaseMathHR1a
public import Chazelle.Core.ShearInv
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# Down phase, math: **H-R1 / H-R2** (`DrvR.HostR1Spec`)

`DownMath.hostR1Spec : DrvR.HostR1Spec`: for region `r` of `N = buildNF I Q L E`, the driver's
host description `H = DrvR.regHost li n N r` is well formed and regular, its polygon is simple with
interior the region and boundary on `∂Q ∪ ⋃ S`, it contains every vertex of `hostPoly Q S (reg r)`,
and every chain `⟨H.poly Q, 0, #points - 1⟩` satisfies the extraction facts `ExtractOK`.

Proof: the walk-order points of `H` represent the host keys of the region cyclically
(`DownMath.walk_rep`); so `H.poly Q` is the host polygon rotated (`LeftInside Q`) or reversed and
rotated (otherwise) (`poly_of_rep`), regular (`edgeOK_of_rep`, `regular_reverse`), with the
geometric facts of the host polygon (`polyFacts_rotate`, `polyFacts_rev`), and the extraction facts
of the host chain (`extractOK_rot`, `extractOK_rev` through the mirror).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open DownHost
open BuildNF (buildNF)
open DrvR (walkItems regHost)

/-- **H-R1 / H-R2.** -/
theorem hostR1Spec : DrvR.HostR1Spec := by
  intro P L E reg r hG hLne hL hperm hsort _hdeg hregs hr Q N S
  classical
  have hQ : Q.Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hdh : DistinctHeights Q := (goodShear_epsOf hG.2).2.1
  have hK : 0 < L.length := List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ hLne)
  have X : RegCtx Q L E reg r := ⟨hQ, hdh, hL, hperm, hsort, hK, hregs, hr⟩
  set li := decide (Mountain.LeftInside Q) with hlidef
  have hli : li = true ↔ Mountain.LeftInside Q := decide_eq_true_iff
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, hwf⟩ := walk_rep X hli
  set WP := (walkItems li Q.n N r).flatMap (wpts li Q.n) with hWP
  -- the context
  have hN : IsNF (interiorModel Q) Q N := isNF_build hQ hL hperm hsort
  have hFam : (interiorModel Q).ChordFamily Q S := hN.1
  have hnc : N.nChords = L.length := nChords_build hQ hL hperm hsort
  have hne : S.Nonempty :=
    ⟨_, (chordPos_attach hN (show 0 < N.nChords by rwx [hnc]) (Or.inl rfl)).1⟩
  have hR : reg r ∈ (interiorModel Q).regions S := hregs.1.1 r hr
  have Xc : Extract.Ctx Q S (reg r) := ⟨hQ, hFam, hne, hR⟩
  set K := nk (interiorModel Q) S (reg r) with hKdef
  have h3 : 3 ≤ K := three_le_nk hQ hFam hne hR
  have hrep' : ∀ j, j < K → RepPt li Q S (reg r) ((i0 + j) % K) (WP.getD j (.vtx 0)) :=
    fun j hj => hrep j (by rwx [hlen])
  have hrot : (⟨WP.map (SymPt.eval Q)⟩ : Polygon) = (hostPoly Q S (reg r)).rotate i0 :=
    poly_of_rep hQ hFam hne hR hli hdh hlen hrep'
  have hedge := edgeOK_of_rep hQ hFam hne hR hdh hlen hrep'
  have hpts := regHost_pts li Q.n N r
  by_cases hLI : Mountain.LeftInside Q
  · -- counterclockwise
    have hl : li = true := hli.2 hLI
    have hH : regHost li Q.n N r = walkItems li Q.n N r := by unfold regHost; rw [ite_eq_left hl]
    rw [ite_eq_left hl] at hpts
    have hpoly : (regHost li Q.n N r).poly Q = (hostPoly Q S (reg r)).rotate i0 := by
      rw [← hrot]; unfold Host.poly; rw [hpts]
    obtain ⟨hs, hint, hbd, hvx⟩ := polyFacts_rotate hQ hFam hne hR i0
    refine ⟨by rwx [hH], ?_, by rwx [hpoly], by rwx [hpoly],
      by rwx [hpoly], by rwx [hpoly], ?_⟩
    · apply hostRegular_of_list
      rwx [hpts]
    · intro C hP hs0 hm
      exact extractOK_rot Xc hgK hgc hgi (hP.trans hpoly) hs0 hm
  · -- clockwise
    have hl : li = false := by
      cases h : li
      · rfl
      · exact absurd (hli.1 h) hLI
    have hH : regHost li Q.n N r = (walkItems li Q.n N r).reverse := by
      urr regHost [hl]
    rw [hl] at hpts
    simp [Bool.false_eq_true, ite_false] at hpts
    rw [← hl] at hpts
    set P' := (regHost li Q.n N r).poly Q with hP'
    have hverts : P'.vertices = (WP.map (SymPt.eval Q)).reverse := by
      rw [hP']
      show ((regHost li Q.n N r).pts Q.n).map (SymPt.eval Q) = _
      rw [hpts, ← hWP, List.map_reverse]
    have hP'n : P'.n = K := by
      show P'.vertices.length = K
      rw [hverts, List.length_reverse, List.length_map, hlen]
    have hrn : ((hostPoly Q S (reg r)).rotate i0).n = K := by
      rw [Existence.n_rotate, hostPoly_n]
    have hP'v : ∀ k, k < K → P'.vtx k = ((hostPoly Q S (reg r)).rotate i0).vtx
        (((hostPoly Q S (reg r)).rotate i0).n - 1 - k) := by
      intro k hk
      rw [hrn, ← hrot]
      show P'.vertices.getD k (0, 0) = (WP.map (SymPt.eval Q)).getD (K - 1 - k) (0, 0)
      rw [hverts, List.getD_eq_getElem _ _ (by simp [hlen]; exact hk), List.getElem_reverse,
        List.getD_eq_getElem _ _ (by sio [hlen])]
      simp [hlen]
    have hfacts : PolyFacts Q S (reg r) P' := polyFacts_rev hQ hFam hne hR i0
      (by rw [hP'n, Existence.n_rotate, hostPoly_n])
      (fun k hk => hP'v k (by rw [Existence.n_rotate, hostPoly_n] at hk; exact hk))
    obtain ⟨hs, hint, hbd, hvx⟩ := hfacts
    refine ⟨?_, ?_, hs, hint, hbd, hvx, ?_⟩
    · rw [hH]; intro it hit; exact hwf it (List.mem_reverse.1 hit)
    · apply hostRegular_of_list
      rw [hpts, ← hWP]
      exact regular_reverse hedge
    · intro C hP hs0 hm
      refine extractOK_rev Xc hgK hgc hgi (by rwx [hP]) (fun k hk => ?_) (hP ▸ hs) hs0 hm
      rw [hP, hP'v k hk, Existence.vtx_rotate _ _ (by rwo [hostPoly_n]), hostPoly_n,
        Existence.n_rotate, hostPoly_n]

end

end DownMath

end Chazelle.Core
