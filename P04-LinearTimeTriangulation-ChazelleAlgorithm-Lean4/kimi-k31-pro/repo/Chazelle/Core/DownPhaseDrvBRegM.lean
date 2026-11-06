module

public import Chazelle.Core.DownPhaseDrvBEnv
public import Chazelle.Core.DownPhaseDrvBSize
public import Chazelle.Core.DownPhaseDrvDRound2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics

/-!
# Down-phase base (D9): the facts of a region for the RAM

For a region `r < K + 1` of the region loop (`BEnv`, `BGood`):

* `far_found`: after the far-end scan over walk edges containing the far walk edge `farW`, the
  best candidate is `farW`;
* `BGood.far_ok`: an emitted index `(k, d)` has a vertex `i`, an interior direction, and its far
  walk edge lies in one of the ranges of the region;
* `BGood.scan_ok`, `BGood.hex_ok` (`K > 0`): the arc scans of the ends of a record are well posed
  and find a match;
* `BGood.ld_ok`: the ranges of the region in memory (`LdOK`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt
open BuildNF (codeLe)
open Chazelle.Visibility (DirInterior chordEnd OpenEdgePt)
open DrvR (qE ivB)

@[expose] public section

/-- **The far-end scan finds the far walk edge**: if the scanned walk edges contain `farW`, the
best candidate is `farW`. -/
theorem far_found {Q : Polygon} (hQ : Q.Simple) (hDH : DistinctHeights Q) {li : Bool} {i d : ℕ}
    (hi : i < Q.n) (hdir : DirInterior Q i (sgnD d)) {ES : ℕ → Prop}
    (hES : ES (farW li Q i d)) {f bw bq : ℕ} (hb : BestOK Q Q.n i (sgnD d) li ES f bw bq) :
    f = 1 ∧ bw = farW li Q i d := by
  obtain ⟨hf1, hf2, hf3⟩ := hb
  obtain ⟨hfw, hfo⟩ := farW_spec hQ hDH li hi hdir
  obtain ⟨q, hcq, -, hoq⟩ := far_cand hQ hDH hi (sgnD_cases d) hdir
  have hq  := openEdge_unique hQ hcq.1 (DownMath.qE_lt li hfw) hoq hfo
  subst hq
  have hf : f = 1 := by
    rcases (by omega : f = 0 ∨ f = 1) with h | h
    · exact absurd hcq (hf3 h _ hES hfw)
    · exact h
  obtain ⟨a1, a2, -, a4, a5⟩ := hf2 hf
  have ho := scan_min hQ hDH hi (sgnD_cases d) hdir hfw hES hfo a2 (by
    obtain ⟨a3⟩ : bq = qE li Q.n bw ∧ True := ⟨(hf2 hf).2.2.1, trivial⟩
    rwx [← a3]) (fun w hw hwn hc => by
      have := a5 w hw hwn hc
      rwa [← (hf2 hf).2.2.1])
  exact ⟨hf, farW_eq hQ hDH li hi hdir a1 ho⟩

/-- The ends of the arcs of `buildNF` are on walk edges. -/
theorem arc_edges_lt {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
    {li : Bool} (B : BaseCtx Q L E reg li) {j : ℕ}
    (hj : j < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length) :
    ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s.edge < Q.n ∧
      ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e.edge < Q.n := by
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; have := B.hK; omega
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) B.hK
  rw [hA] at hj
  have hs := DrvD.arc_s (M := interiorModel Q) (Q := Q) (E := E) B.hK hj
  have he := DrvD.arc_e (M := interiorModel Q) (Q := Q) (E := E) B.hK hj
  obtain ⟨sn, -, -⟩ := evPos_ok B (DrvD.gs_lt_len hj)
  obtain ⟨en, -, -⟩ := evPos_ok B (Nat.mod_lt (DrvD.gs (interiorModel Q) Q L E j + 1) hE)
  rw [hs, he]
  exact ⟨sn, en⟩

namespace BGood

variable {E : BEnv} (hE : BGood E)
include hE

omit hE in
theorem getD_mem (_hE : BGood E) {l : List ℕ} {t : ℕ} (ht : t < l.length) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  exact List.getElem_mem ht

/-- **An emitted index**: a vertex `i`, an interior direction, and the far walk edge in one of
the ranges of the region. -/
theorem far_ok {r : ℕ} (hr : r < E.K + 1) {k d : ℕ} (hkd : (k, d) ∈ emIdx E.Q (E.pts r)) :
    ∃ i, qvx E.Q ((E.pts r).getD k (.vtx 0)) = some i ∧ i < E.P.n ∧ d ≤ 1 ∧
      DirInterior E.Q i (sgnD d) ∧
      ESr E.P.n (E.stF r) (E.cntF r) (E.nRg r) 0 (farW E.li E.Q i d) := by
  obtain ⟨S, R, hFam, hR⟩ := hE.regOK hr
  obtain ⟨i, hi, hin, hk, hd, -, -, hdir, -⟩ := emIdx_facts hE.hQ hFam hR (hE.pts_lt hr) hkd
  obtain ⟨hfw, hfo⟩ := farW_spec hE.hQ hE.hDH E.li hin hdir
  have hQn := hE.hQn
  refine ⟨i, hi, by rwx [← hQn], hd, hdir, ?_⟩
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · refine Or.inl ⟨0, by uro BEnv.nRg [ite_eq_left hK], farW E.li E.Q i d, ?_, ?_⟩
    · unfold BEnv.cntF; rwx [ite_eq_left hK, ← hQn]
    · unfold BEnv.stF; rw [ite_eq_left hK, Nat.zero_add, Nat.mod_eq_of_lt (by rwx [← hQn])]
  · have B := hE.ctx hK
    have hr' : r < E.N.nRegions := by rwx [hE.nRegions]
    -- the record
    set x := recAt E.li E.Q (E.pts r) (k, d) with hx
    have hxm : x ∈ regList E.li E.Q (regPts E.li E.Q.n E.N r) := by
      rw [← pts_pos hK]; exact List.mem_map_of_mem hkd
    have hxv : x = vtrip E.li E.Q.n i d (farW E.li E.Q i d) := by
      rw [hx]; urr recAt [hi]
    obtain ⟨hRo, hl⟩ := region_facts (B.rc hr') hE.hli
    obtain ⟨-, -, -, -, hpl, hpr, -⟩ := regList_sound hE.hQ hE.hDH hE.hli B.fam hRo hl hxm
    -- the far end
    set y : WPos := if d = 0 then (recOf x).rpos else (recOf x).lpos with hy
    have hye : y.edge = farW E.li E.Q i d := by
      rw [hy, hxv]; unfold vtrip; split_ifs <;> rfl
    have hyp : ProperPos E.I E.Q E.Q.n y := by rw [hy]; split_ifs; exact hpr; exact hpl
    obtain ⟨j, hjm, hj, hcl⟩ := ends_on_arcs B hr' hxm (y := y) (by
      rw [hy]; split_ifs; exact Or.inr rfl; exact Or.inl rfl)
    have hky : E.I.key E.Q y = (farW E.li E.Q i d : ℝ) + E.I.param E.Q y := by
      show (y.edge : ℝ) + _ = _; rw [hye]
    rw [hky] at hcl
    obtain ⟨u, hu, hsu⟩ := closedArc_range B hj hfw hyp.1 hyp.2.1 hcl
    obtain ⟨t, ht, htj⟩ := List.mem_iff_getElem.1 hjm
    have hg : (E.N.region r).arcs.getD t 0 = j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some, htj]
    refine Or.inl ⟨t, by unfold BEnv.nRg; rwx [ite_eq_right (by omega)], u, ?_, ?_⟩
    · unfold BEnv.cntF BEnv.arcR; rwx [ite_eq_right (by omega), hg, ← hQn]
    · unfold BEnv.stF BEnv.arcR; rw [ite_eq_right (by omega), hg, ← hQn]; exact hsu.symm

/-- The words of the descriptor agree. -/
theorem desc_m {m : ℕ → ℕ} (hm : ∀ a, a < E.B₂ → m a = E.m₀ a) :
    ModelDescAt m E.MD E.Q E.I ∧ ModelDescWF E.P E.B₂ m E.MD := by
  have h1 := DrvD.desc_one hE.hMD
  have hMDW := hE.hMDW
  refine ⟨?_, ⟨by omega, fun h0 => ?_⟩⟩
  · rcases hE.hMD with ⟨h0, -⟩ | ⟨-, h2, h3⟩
    · omega
    · exact Or.inr ⟨by rwx [hm _ (by omega)], by rwx [hm _ (by omega)], h3⟩
  · rwo [hm _ (by omega)] at h0

/-- The handle words and the region records lie below `B₂`. -/
theorem areas {r : ℕ} (hr : r < E.K + 1) :
    E.H + 7 < E.B₂ ∧ E.m₀ (E.H + 5) + 5 * r + 4 < E.B₂ := by
  have h := Gran.nf_areas hE.hNF
  exact ⟨h.1, h.2.2.1 r (by rwx [hE.nRegions])⟩

/-- **The arc scans of the ends of a record are well posed** (`K > 0`). -/
theorem scan_ok (hK : 0 < E.K) {r : ℕ} (hr : r < E.K + 1) {x : ℕ × ℕ × ℕ} (hx : x ∈ E.recs r)
    {m : ℕ → ℕ} (hm : ∀ a, a < E.B₂ → m a = E.m₀ a) (_hmW : ∀ a, m a ≤ E.W) {s : ℕ}
    (hs : s < 2) :
    DrvD.ScanGood E.P E.W E.I E.N r (DrvD.endPos x s) m E.MD (E.m₀ (E.H + 4)) (E.LP r) := by
  have B := hE.ctx hK
  have hr' : r < E.N.nRegions := by rwx [hE.nRegions]
  have hGM : GoodModel E.I := Or.inr ⟨E.Q, hE.hQ, rfl⟩
  obtain ⟨hRo, hl⟩ := region_facts (B.rc hr') hE.hli
  have hxm : x ∈ regList E.li E.Q (regPts E.li E.Q.n E.N r) := by
    unfold BEnv.recs at hx; rwa [pts_pos hK] at hx
  obtain ⟨-, -, -, hatt, hpl, hpr, -⟩ := regList_sound hE.hQ hE.hDH hE.hli B.fam hRo hl hxm
  obtain ⟨hMDm, hwfm⟩ := hE.desc_m hm
  have hBW : E.B₂ ≤ E.W := by have := hE.hBW; omega
  have hQn := hE.hQn
  have hp : ProperPos E.I E.Q E.P.n (DrvD.endPos x s) ∧ (DrvD.endPos x s).edge < E.I.W.n := by
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · rw [← hQn]; exact ⟨hpl, hatt.1.1⟩
    · rw [← hQn]; exact ⟨hpr, hatt.2.1⟩
  have h := DrvD.scanGood_of hGM hE.hG hE.hWh hE.hok hE.hperm hE.hsort hK hE.hregs
    (hE.hNF.transport hm) hBW hwfm hMDm hr hp.2 (by
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [DrvD.endPos]) hp.1
  obtain ⟨a1, a2⟩ := hE.areas hr
  rw [hm (E.H + 4) (by omega), hm (E.H + 7) (by omega), hm (E.H + 5) (by omega),
    hm (E.m₀ (E.H + 5) + 5 * r + 1) (by omega)] at h
  exact h

/-- **The arc scans of the ends of a record find a match** (`K > 0`). -/
theorem hex_ok (hK : 0 < E.K) {r : ℕ} (hr : r < E.K + 1) {x : ℕ × ℕ × ℕ} (hx : x ∈ E.recs r)
    {s : ℕ} (hs : s < 2) :
    ∃ j ∈ (E.N.region r).arcs, DrvD.matchB E.N.arcs.length j
      (DrvD.tA E.I E.Q E.N (DrvD.endPos x s) j) (DrvD.tB E.I E.Q E.N (DrvD.endPos x s) j) =
        true := by
  have B := hE.ctx hK
  have hr' : r < E.N.nRegions := by rwx [hE.nRegions]
  have hxm : x ∈ regList E.li E.Q (regPts E.li E.Q.n E.N r) := by
    unfold BEnv.recs at hx; rwa [pts_pos hK] at hx
  refine scan_hex B hr' hxm ?_
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **A region has at most five arcs** (degree at most `4`). -/
theorem arcs_le5 {r : ℕ} (hr : r < E.K + 1) : (E.N.region r).arcs.length ≤ 5 := by
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · have hreg := DrvD.region_buildNF (M := E.I) (Q := E.Q) (L := E.L) (E := E.E) hr
    have hlen : E.E.length = 2 * E.L.length := by
      rw [hE.hperm.length_eq, List.length_range]
    have hA := DrvD.arcs_length_le (M := E.I) (Q := E.Q) (L := E.L) (E := E.E) hlen
    rw [hreg]
    unfold BuildNF.regArcs
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_range]
    have : (BuildNF.buildNF E.I E.Q E.L E.E).arcs.length = (BuildNF.arcList E.I E.Q E.L E.E).length :=
      rfl
    have hK' : E.L.length = 0 := hK
    omega
  · have B := hE.ctx hK
    have hr' : r < E.N.nRegions := by rwx [hE.nRegions]
    have h1 := arcs_length_le B hr'
    have h2 := hE.hdeg (E.reg r) (hE.hregs.1.1 r hr')
    exact le_trans h1 (Nat.add_le_add_right h2 1)

theorem nRg_le5 {r : ℕ} (hr : r < E.K + 1) : E.nRg r ≤ 5 := by
  unfold BEnv.nRg; split_ifs
  · omega
  · exact hE.arcs_le5 hr

/-- **A region has an arc.** -/
theorem arcs_pos {r : ℕ} (hr : r < E.K + 1) : 0 < (E.N.region r).arcs.length := by
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · have hr0 : r = 0 := by omega
    subst hr0
    rw [DrvD.region_buildNF (M := E.I) (Q := E.Q) (L := E.L) (E := E.E) hr]
    have hK'  := hK
    simp [BuildNF.regArcs, BuildNF.arcList, hK']
  · have hM := walkAx_interiorModel hE.hQ
    have hNF  := DownMath.isNF_build hE.hQ hE.hok hE.hperm hE.hsort
    have hnc  := DownMath.nChords_build hE.hQ hE.hok hE.hperm hE.hsort
    have hne : (E.N.F E.I E.Q).Nonempty :=
      ⟨_, (DownMath.chordPos_attach hNF (show 0 < E.N.nChords by rwx [hnc])
        (Or.inl rfl)).1⟩
    exact (Restore.region_arc hM hNF hE.hregs hne (by rwx [hE.nRegions])).1

/-- The arc list of a region lies below `B₂`. -/
theorem LP_lt {r : ℕ} (hr : r < E.K + 1) : E.LP r < E.B₂ := by
  have := DrvD.arcList_lt hE.hNF (r := r) (by rwx [hE.nRegions]) (t := 0)
    (hE.arcs_pos hr)
  ufo BEnv.LP

/-- The number of arcs of a region in memory. -/
theorem nA_eq {r : ℕ} (hr : r < E.K + 1) :
    (E.N.region r).arcs.length = E.m₀ (E.m₀ (E.H + 5) + 5 * r) := by
  have hR : r < E.N.regions.length := by
    have := hE.nRegions; ufo NF.nRegions at this
  exact ((hE.hNF.nfAt.2.2.2.2.2.2.2.1 r hR).1).symm

/-- **The ranges of a region in memory.** -/
theorem ld_ok {r : ℕ} (hr : r < E.K + 1) (c : Config)
    (hm : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a) (h12 : c.nreg 212012 = E.K)
    (h14 : c.nreg 216014 = E.m₀ (E.H + 4)) (h33 : 0 < E.K → c.nreg 212033 = E.LP r) {t : ℕ}
    (ht : t < E.nRg r) :
    LdOK c E.P.n t (E.stF r t) (E.cntF r t) ∧
      (0 < c.nreg 212012 → c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3 ≤ E.W) ∧
      (0 < c.nreg 212012 → c.nreg 212033 + E.nRg r ≤ E.W) := by
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · refine ⟨Or.inl ⟨h12.trans hK, by unfold BEnv.stF; rw [ite_eq_left hK],
      by unfold BEnv.cntF; rw [ite_eq_left hK]⟩, fun h => by omega, fun h => by omega⟩
  · have B := hE.ctx hK
    have hr' : r < E.N.nRegions := by rwx [hE.nRegions]
    have hR : r < E.N.regions.length := by
      have := hE.nRegions; ufo NF.nRegions at this
    have htn : t < (E.N.region r).arcs.length := by
      unfold BEnv.nRg at ht; rwa [ite_eq_right (by omega)] at ht
    have hNAt := hE.hNF.nfAt
    have hBW : E.B₂ ≤ E.W := by have := hE.hBW; omega
    set j := (E.N.region r).arcs.getD t 0 with hjd
    have hjm : j ∈ (E.N.region r).arcs := getD_mem hE htn
    have hjA : j < E.N.arcs.length := ((hE.hregs.2.2.1.2.2.2 r hr' j).1 hjm).1
    have hlp : E.LP r + t < E.B₂ := DrvD.arcList_lt hE.hNF hr' htn
    have hlpj : c.nmem (E.LP r + t) = j := by
      rw [hm _ hlp]; exact ((hNAt.2.2.2.2.2.2.2.1 r hR).2.2.2.1 t htn)
    have hAB : E.m₀ (E.H + 4) + 5 * j + 4 < E.B₂ := (Gran.nf_areas hE.hNF).2.2.2.2.1 j hjA
    obtain ⟨-, a1, -, a3, -⟩ := hNAt.2.2.2.2.2.2.1 j hjA
    obtain ⟨sn, en⟩ := arc_edges_lt B hjA
    have hQn := hE.hQn
    unfold LdOK
    rw [h33 hK, h14, hlpj]
    have hlast : E.LP r + E.nRg r ≤ E.B₂ := by
      have := DrvD.arcList_lt hE.hNF hr' (t := (E.N.region r).arcs.length - 1) (by omega)
      unfold BEnv.nRg; ruo [ite_eq_right (by omega)] BEnv.LP
    refine ⟨Or.inr ⟨by omega, ?_, ?_, ?_, ?_⟩, fun _ => by omega, fun _ => by omega⟩
    · unfold BEnv.stF BEnv.arcR; rw [ite_eq_right (by omega), hm _ (by omega), a1]
    · unfold BEnv.stF BEnv.arcR; rw [ite_eq_right (by omega), ← hQn]; exact sn
    · rw [hm _ (by omega), a3, ← hQn]; exact en
    · unfold BEnv.cntF BEnv.stF BEnv.arcR arcCnt
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hm _ (by omega), a3]

end BGood

end

end DrvB

end Chazelle.Core
