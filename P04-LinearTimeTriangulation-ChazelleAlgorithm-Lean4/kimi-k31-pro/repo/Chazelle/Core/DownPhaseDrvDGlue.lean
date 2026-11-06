module

public import Chazelle.Core.DownPhaseDrvDScan
public import Chazelle.Core.DownPhaseDrvDRMath
public import Chazelle.Core.RestoreRegArc
public import Chazelle.Core.GranNFBounds
public import Chazelle.Core.NFLocateSpec
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Down-phase restoration rounds (D8), part 6: the scan of a new chord end is well posed

For the normal form `N = BuildNF.buildNF M Q L E` in memory and a chord `t` found for region `r`
(`Restore.FoundOK`):

* `scanGood_of`: the scan data (`ScanGood`) of an end `x` of `t` in region `r`, read from the
  normal-form layout (`NFAt`): the arc list of `r` and the arc records, below the bound;
* `hex_of`: some arc of `r` matches each end of `t` (`exists_closedArc`, `match_of_closedArc`);
* `endPos_*`: the ends of `t` as scan inputs.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs
open BuildNF (codeLe wposOf)

@[expose] public section

variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The arc list of a region lies below the bound of a robust normal form. -/
theorem arcList_lt {m : ℕ → ℕ} {B E' : ℕ} {N : NF} (h : NFWithin m B E' N) {r : ℕ}
    (hr : r < N.nRegions) {t : ℕ} (ht : t < (N.region r).arcs.length) :
    m (B + 7) + m (m (B + 5) + 5 * r + 1) + t < E' := by
  have hp : m (B + 5) + 5 * r + 1 < E' := by
    have := (Gran.nf_areas h).2.2.1 r hr; omega
  have hB  := (Gran.nf_areas h).1
  exact Gran.robust_addr3 (b₁ := B + 7) (p₂ := m (B + 5) + 5 * r + 1) (t := t)
    (v := (N.region r).arcs.getD t 0) hp (fun m' hm' => by
      have e5 : m' (B + 5) = m (B + 5) := hm' _ (by omega)
      have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht
      rw [e5] at this
      exact this)

/-- The ends of a found chord are proper positions of the walk at a vertex height. -/
theorem endPos_props (_hGM : GoodModel M) {N : NF} {reg : ℕ → Set Point} {r : ℕ}
    {t : ℕ × ℕ × ℕ} (hf : Restore.FoundOK M (Qof P) N reg r t) {s : ℕ} (hs : s < 2) :
    (endPos t s).edge < M.W.n ∧ 1 ≤ (endPos t s).hgt ∧ ProperPos M (Qof P) P.n (endPos t s) ∧
      Chazelle.Chain.SideAttach M.W ((recOf t).toSet M (Qof P)) (endPos t s).edge
        (M.param (Qof P) (endPos t s)) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hA : Chazelle.Chain.SideAttach M.W ((recOf t).toSet M (Qof P)) (endPos t s).edge
      (M.param (Qof P) (endPos t s)) := by
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact hf.1.1
    · exact hf.1.2
  have hh : (endPos t s).hgt = t.1 + 1 := by unfold endPos; split_ifs <;> rfl
  obtain ⟨he, h0, h1, -⟩ := id hA
  refine ⟨he, by omega, ⟨h0, h1, ?_⟩, hA⟩
  have := hf.2.1
  omega

/-- **The scan data of an end of a chord of region `r`.** -/
theorem scanGood_of (hGM : GoodModel M) {W : ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hok : ChordTriplesOK M (Qof P) L) (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe M (Qof P) L)) (hK : 0 < L.length) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs M (Qof P) (BuildNF.buildNF M (Qof P) L E) reg) {m : ℕ → ℕ} {H B MD : ℕ}
    (hNW : NFWithin m H B (BuildNF.buildNF M (Qof P) L E)) (hBW : B ≤ W)
    (hwf : ModelDescWF P B m MD) (hMD : ModelDescAt m MD (Qof P) M) {r : ℕ}
    (hr : r < L.length + 1) {x : WPos} (hxe : x.edge < M.W.n) (hx1 : 1 ≤ x.hgt)
    (hxp : ProperPos M (Qof P) P.n x) :
    ScanGood P W M (BuildNF.buildNF M (Qof P) L E) r x m MD (m (H + 4))
      (m (H + 7) + m (m (H + 5) + 5 * r + 1)) := by
  have hM := walkAx_of_goodModel hGM
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hNF, -, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
  set N := BuildNF.buildNF M (Qof P) L E with hN
  have hR : N.nRegions = L.length + 1 := by simp [hN, NF.nRegions, BuildNF.buildNF]
  have hr' : r < N.nRegions := by rwx [hR]
  have hNAt := hNW.nfAt
  have hne : (N.F M (Qof P)).Nonempty := by
    refine ⟨(N.chord 0).toSet M (Qof P), N.chord 0, ?_, rfl⟩
    unfold NF.chord
    have h0 : 0 < N.chords.length := by simp [hN, BuildNF.buildNF]; exact hK
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some]
    exact List.getElem_mem h0
  obtain ⟨hnA, -, -⟩ := Restore.region_arc hM hNF hregs hne hr'
  obtain ⟨hDW, hCW⟩ := NFLoc.locChainWF_of hwf hBW hWh
  have hAOK := hregs.2.2.1
  have hareas := Gran.nf_areas hNW
  have hA : 0 < N.arcs.length := by
    have hm : (N.region r).arcs.getD 0 0 ∈ (N.region r).arcs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnA, Option.getD_some]
      exact List.getElem_mem hnA
    exact lt_of_le_of_lt (Nat.zero_le _) ((hAOK.2.2.2 r hr' _).1 hm).1
  refine ⟨hG, hWh, hDW, hCW, hMD, hxe, hx1, hxp, ?_, ?_, fun t ht => ?_, fun j hj => ?_⟩
  · have := arcList_lt hNW hr' (t := (N.region r).arcs.length - 1) (by omega)
    omega
  · have := hareas.2.2.2.2.1 (N.arcs.length - 1) (by omega)
    omega
  · have := (hNAt.2.2.2.2.2.2.2.1 r hr').2.2.2.1 t ht
    exact this
  · have hjA := ((hAOK.2.2.2 r hr' j).1 hj).1
    obtain ⟨-, a1, a2, a3, a4⟩ := hNAt.2.2.2.2.2.2.1 j hjA
    obtain ⟨-, -, -, -, -, -, -, hpp⟩ := hNF.2.2.2
    obtain ⟨hps, hpe⟩ := hpp j hjA
    rw [hQn] at hps hpe
    have hA' := arcs_length (M := M) (Q := Qof P) (E := E) hK
    have hElen : E.length = 2 * L.length := by rw [hperm.length_eq, List.length_range]
    have hjg : j < (BuildNF.gapStarts M (Qof P) L E).length := by rwx [← hA']
    -- the end of arc `j` is an event position
    have hev : (E.getD ((gs M (Qof P) L E j + 1) % E.length) 0) < 2 * L.length := by
      have hi : (gs M (Qof P) L E j + 1) % E.length < E.length := Nat.mod_lt _ (by omega)
      have hmem : E.getD ((gs M (Qof P) L E j + 1) % E.length) 0 ∈ E := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      simpa using hperm.mem_iff.1 hmem
    have he := arc_e (M := M) (Q := Qof P) (E := E) hK hjg
    refine ⟨hjA, ?_, ?_, ?_, ?_, hps, hpe, ?_, ?_⟩
    · rw [← a1]
    · rw [← a2]
    · rw [← a3]
    · rw [← a4]
    · rwo [he, BuildRam.wposOf_hgt]
    · rw [he]; exact BuildRam.edge_lt hok hev

/-- **Some arc of region `r` matches each end of a chord found for `r`.** -/
theorem hex_of (hGM : GoodModel M) (hok : ChordTriplesOK M (Qof P) L)
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M (Qof P) L))
    (hK : 0 < L.length) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs M (Qof P) (BuildNF.buildNF M (Qof P) L E) reg) {r : ℕ}
    (hr : r < (BuildNF.buildNF M (Qof P) L E).nRegions) {t : ℕ × ℕ × ℕ}
    (hf : Restore.FoundOK M (Qof P) (BuildNF.buildNF M (Qof P) L E) reg r t) {s : ℕ} (hs : s < 2) :
    ∃ j ∈ ((BuildNF.buildNF M (Qof P) L E).region r).arcs,
      matchB (BuildNF.buildNF M (Qof P) L E).arcs.length j
        (tA M (Qof P) (BuildNF.buildNF M (Qof P) L E) (endPos t s) j)
        (tB M (Qof P) (BuildNF.buildNF M (Qof P) L E) (endPos t s) j) = true := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨hNF, -, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
  set N := BuildNF.buildNF M (Qof P) L E with hN
  have hne : (N.F M (Qof P)).Nonempty := by
    refine ⟨(N.chord 0).toSet M (Qof P), N.chord 0, ?_, rfl⟩
    unfold NF.chord
    have h0 : 0 < N.chords.length := by simp [hN, BuildNF.buildNF]; exact hK
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some]
    exact List.getElem_mem h0
  have hElen : E.length = 2 * L.length := by rw [hperm.length_eq, List.length_range]
  obtain ⟨-, -, -, hA⟩ := endPos_props (P := P) hGM hf hs
  obtain ⟨j, hj, hjA, hcl⟩ := exists_closedArc hM hNF hregs hne hr hf.2.2.1 hf.2.2.2 hA
  refine ⟨j, hj, match_of_closedArc hK (by omega) hjA hcl (by sirfl [tA])
    (by sirfl [tB])⟩

end

end DrvD

end Chazelle.Core
