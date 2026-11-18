module

public import Chazelle.Core.DownPhaseDrvXDef

/-!
# Down phase, extraction (D6): the setting

`XHyp`: the hypotheses of the extraction (region `r` of `N = buildNF I Q L E`, the region chain
`C = ⟨H.poly Q, 0, m⟩` of `H = regHost li n N r`, a normal form `NR` of `chainModel C`).

`XCtx … i0 g`: the derived facts (from the proof of H-R1, `DownMath.walk_rep`): the host point
`k` of `H` represents the host key `σ k = (i0 + ρ k) mod K` of the region (`ρ k = k` if `li`,
`K - 1 - k` otherwise, `K = nk`), so `C.P.vtx k = (hostPoly Q S R).vtx (σ k)`; the host key `g`
before `i0` is a chord gap.  `XHyp.ctx`: the context exists.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set DownHost DownMath
open BuildNF (buildNF)
open DrvR (regHost walkItems)

/-- **The hypotheses of the extraction.** -/
structure XHyp (P : Polygon) (li : Bool) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (reg : ℕ → Set Point) (r : ℕ) (C : Chain) (NR : NF) : Prop where
  hG : GoodEnv P
  hli : li = true ↔ Mountain.LeftInside (Qof P)
  hLne : L ≠ []
  hL : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L
  hperm : E.Perm (List.range (2 * L.length))
  hsort : E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L)
  hregs : Restore.NFRegs (interiorModel (Qof P)) (Qof P)
    (buildNF (interiorModel (Qof P)) (Qof P) L E) reg
  hr : r < (buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions
  hCP : C.P = (regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r).poly (Qof P)
  hCs : C.s = 0
  hCm : C.m + 1 = C.P.n
  hNR : IsNF (chainModel C) (Qof P) NR

/-- The walk-order index of host point `k`. -/
def rho (li : Bool) (K k : ℕ) : ℕ := if li then k else K - 1 - k

theorem rho_lt (li : Bool) {K k : ℕ} (hk : k < K) : rho li K k < K := by
  unfold rho; split_ifs <;> omega

/-- **The context of the extraction.** -/
structure XCtx (P : Polygon) (li : Bool) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (reg : ℕ → Set Point) (r : ℕ) (C : Chain) (NR : NF) (i0 g : ℕ) : Prop where
  X : XHyp P li L E reg r C NR
  hg : g < nk (interiorModel (Qof P))
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r)
  hgc : ChordGap (interiorModel (Qof P))
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) g
  hgi : (g + 1) % nk (interiorModel (Qof P))
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) =
      i0 % nk (interiorModel (Qof P))
        ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r)
  hn : C.P.n = nk (interiorModel (Qof P))
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r)
  hrep : ∀ k, k < nk (interiorModel (Qof P))
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) →
    RepPt li (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
      (Qof P)) (reg r)
      ((i0 + rho li (nk (interiorModel (Qof P))
        ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r))
          k) % nk (interiorModel (Qof P))
        ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r))
      (hpt (Qof P).n (regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r) k)
  hvtx : ∀ k, k < nk (interiorModel (Qof P))
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) →
    C.P.vtx k = (hostPoly (Qof P)
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r)).vtx
      ((i0 + rho li (nk (interiorModel (Qof P))
        ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r))
          k) % nk (interiorModel (Qof P))
        ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r))
  hfacts : PolyFacts (Qof P)
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) C.P
  hext : DownDrv.ExtractOK (Qof P)
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) C
  hbd : C.P.boundary = (hostPoly (Qof P)
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r)).boundary

namespace XHyp

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF}

theorem hQ (X : XHyp P li L E reg r C NR) : (Qof P).Simple :=
  (shearInvariance (epsOf P) P).1 X.hG.1

theorem hdh (X : XHyp P li L E reg r C NR) : DistinctHeights (Qof P) :=
  (goodShear_epsOf X.hG.2).2.1

theorem hK (X : XHyp P li L E reg r C NR) : 0 < L.length :=
  List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ X.hLne)

theorem regCtx (X : XHyp P li L E reg r C NR) : RegCtx (Qof P) L E reg r :=
  ⟨X.hQ, X.hdh, X.hL, X.hperm, X.hsort, X.hK, X.hregs, X.hr⟩

theorem hN (X : XHyp P li L E reg r C NR) :
    IsNF (interiorModel (Qof P)) (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) :=
  isNF_build X.hQ X.hL X.hperm X.hsort

theorem hFam (X : XHyp P li L E reg r C NR) :
    (interiorModel (Qof P)).ChordFamily (Qof P)
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) :=
  X.hN.1

theorem hne (X : XHyp P li L E reg r C NR) :
    ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)).Nonempty := by
  have hnc := nChords_build X.hQ X.hL X.hperm X.hsort
  exact ⟨_, (chordPos_attach X.hN (show 0 < (buildNF (interiorModel (Qof P)) (Qof P) L E).nChords
    by rw [hnc]; exact X.hK) (Or.inl rfl)).1⟩

theorem hR (X : XHyp P li L E reg r C NR) :
    reg r ∈ (interiorModel (Qof P)).regions
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) :=
  X.hregs.1.1 r X.hr

theorem ectx (X : XHyp P li L E reg r C NR) :
    Extract.Ctx (Qof P)
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) (reg r) :=
  ⟨X.hQ, X.hFam, X.hne, X.hR⟩

/-- **The context exists.** -/
theorem ctx (X : XHyp P li L E reg r C NR) : ∃ i0 g, XCtx P li L E reg r C NR i0 g := by
  classical
  set Q := Qof P with hQdef
  set N := buildNF (interiorModel Q) Q L E with hNdef
  set S := N.F (interiorModel Q) Q with hSdef
  have hQ := X.hQ
  have hdh := X.hdh
  have hli := X.hli
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, -⟩ := walk_rep X.regCtx hli
  set WP := (walkItems li Q.n N r).flatMap (wpts li Q.n) with hWP
  have hFam := X.hFam
  have hne := X.hne
  have hR := X.hR
  have Xc := X.ectx
  set K := nk (interiorModel Q) S (reg r) with hKdef
  have h3 : 3 ≤ K := three_le_nk hQ hFam hne hR
  have hrep' : ∀ j, j < K → RepPt li Q S (reg r) ((i0 + j) % K) (WP.getD j (.vtx 0)) :=
    fun j hj => hrep j (by rw [hlen]; exact hj)
  have hrot : (⟨WP.map (SymPt.eval Q)⟩ : Polygon) = (hostPoly Q S (reg r)).rotate i0 :=
    poly_of_rep hQ hFam hne hR hli hdh hlen hrep'
  have hpts := regHost_pts li Q.n N r
  -- the host points in walk order
  have hHp : ∀ k, k < K → hpt Q.n (regHost li Q.n N r) k = WP.getD (rho li K k) (.vtx 0) := by
    intro k hk
    unfold hpt rho
    by_cases hl : li = true
    · rw [ite_eq_left hl] at hpts ⊢; rw [hpts]
    · rw [ite_eq_right hl] at hpts ⊢
      rw [hpts, List.getD_eq_getElem _ _ (by rw [List.length_reverse, ← hWP, hlen]; exact hk),
        List.getElem_reverse, List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
      simp only [← hWP, hlen]
  have hHlen : ((regHost li Q.n N r).pts Q.n).length = K := by
    by_cases hl : li = true
    · rw [ite_eq_left hl] at hpts; rw [hpts, ← hWP, hlen]
    · rw [ite_eq_right hl] at hpts; rw [hpts, List.length_reverse, ← hWP, hlen]
  have hn : C.P.n = K := by
    rw [X.hCP]; show (((regHost li Q.n N r).pts Q.n).map (SymPt.eval Q)).length = K
    rw [List.length_map, hHlen]
  have hrepH : ∀ k, k < K → RepPt li Q S (reg r) ((i0 + rho li K k) % K)
      (hpt Q.n (regHost li Q.n N r) k) := by
    intro k hk
    rw [hHp k hk]
    exact hrep' _ (rho_lt li hk)
  have hvtx : ∀ k, k < K → C.P.vtx k = (hostPoly Q S (reg r)).vtx ((i0 + rho li K k) % K) := by
    intro k hk
    have hι : (i0 + rho li K k) % K < K := Nat.mod_lt _ (by omega)
    rw [hostPoly_vtx hι, ← rep_eval hQ hFam hne hR hli hdh hι (hrepH k hk), X.hCP]
    show (((regHost li Q.n N r).pts Q.n).map (SymPt.eval Q)).getD k (0, 0) = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hHlen]; exact hk), List.getElem_map]
    unfold hpt
    rw [List.getD_eq_getElem _ _ (by rw [hHlen]; exact hk)]
  -- polygon facts and extraction facts
  have hrn : ((hostPoly Q S (reg r)).rotate i0).n = K := by
    rw [Existence.n_rotate, hostPoly_n]
  by_cases hLI : Mountain.LeftInside Q
  · have hl : li = true := hli.2 hLI
    have hpoly : C.P = (hostPoly Q S (reg r)).rotate i0 := by
      apply poly_eq_of_vtx (by rw [hn, hrn])
      intro k hk
      rw [hn] at hk
      rw [hvtx k hk, Existence.vtx_rotate _ _ (by rw [hostPoly_n]; exact hk), hostPoly_n]
      unfold rho; rw [ite_eq_left hl]
    refine ⟨i0, g, ⟨X, hgK, hgc, hgi, hn, hrepH, hvtx, ?_, ?_, ?_⟩⟩
    · rw [hpoly]; exact polyFacts_rotate hQ hFam hne hR i0
    · exact extractOK_rot Xc hgK hgc hgi hpoly X.hCs X.hCm
    · rw [hpoly, Existence.boundary_rotate]
  · have hl : li = false := by
      cases h : li
      · rfl
      · exact absurd (hli.1 h) hLI
    have hPv : ∀ k, k < K → C.P.vtx k = ((hostPoly Q S (reg r)).rotate i0).vtx
        (((hostPoly Q S (reg r)).rotate i0).n - 1 - k) := by
      intro k hk
      rw [hvtx k hk, hrn, Existence.vtx_rotate _ _ (by rw [hostPoly_n]; omega), hostPoly_n]
      unfold rho; rw [hl]; rfl
    refine ⟨i0, g, ⟨X, hgK, hgc, hgi, hn, hrepH, hvtx, ?_, ?_, ?_⟩⟩
    · exact polyFacts_rev hQ hFam hne hR i0 (by rw [hn, hrn])
        (fun k hk => hPv k (by rw [hrn] at hk; exact hk))
    · refine extractOK_rev Xc hgK hgc hgi hn (fun k hk => ?_)
        (polyFacts_rev hQ hFam hne hR i0 (by rw [hn, hrn])
          (fun k hk => hPv k (by rw [hrn] at hk; exact hk))).1 X.hCs X.hCm
      rw [hvtx k hk]
      unfold rho; rw [hl]; rfl
    · rw [Mountain.rev_boundary (by rw [hn, hrn]) (fun k hk => hPv k (by rw [hrn] at hk; exact hk)),
        Existence.boundary_rotate]

end XHyp

end

end DrvX

end Chazelle.Core
