module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBFam
public import Chazelle.Core.DownPhaseDrvDScan

/-!
# Down-phase base (D9): the ends of a new chord on the arcs of its region

For `K > 0` the base locates both ends of every new chord on the closed arcs of its region (the
buckets of the splice, through the arc scan `DrvD.scanS` of the restoration rounds), and finds
the far end by a scan over the walk edges of the arcs of the region.

* `ends_on_arcs`: both ends of an emitted record lie on closed arcs of the region
  (`Restore.attach_closedArc`, the arc records `ArcsOK`);
* `scan_hex`: the arc scan finds a match (`DrvD.match_of_closedArc`);
* `arcCnt`: the walk edges `s.edge, …, e.edge` of an arc (cyclically); `last_arc_edges`: the last
  (wrapping) arc of `buildNF` starts and ends on distinct walk edges; **`closedArc_range`**: a
  position on a closed arc lies on one of its walk edges.
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt sideInArc)
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE walkItems regHost)
open BuildNF (codeLe wposOf gapStarts)

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-! ## The ends of a new chord -/

section
variable (B : BaseCtx Q L E reg li) {r : ℕ} (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) {x : ℕ × ℕ × ℕ} (hx : x ∈ regList li Q (regPts li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r)) {y : WPos} (hy : y = (recOf x).lpos ∨ y = (recOf x).rpos)
include B hr x hx hy
/-- **Both ends of an emitted record lie on closed arcs of its region.** -/
theorem ends_on_arcs :
    ∃ j ∈ ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs,
      j < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length ∧
      Restore.ClosedArc ((interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s)
        ((interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e)
        ((interiorModel Q).key Q y) := by
  set N := BuildNF.buildNF (interiorModel Q) Q L E with hN
  obtain ⟨hR, hl⟩ := region_facts (B.rc hr) B.hli
  obtain ⟨hcQ, hcS, hcR, hatt, -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR hl hx
  have hFam := B.fam
  have hM := walkAx_interiorModel B.hQ
  have hnc : N.nChords = L.length := DownMath.nChords_build B.hQ B.hL B.hperm B.hsort
  have hNF : IsNF (interiorModel Q) Q N := DownMath.isNF_build B.hQ B.hL B.hperm B.hsort
  have hne : (N.F (interiorModel Q) Q).Nonempty :=
    ⟨_, (DownMath.chordPos_attach hNF (show 0 < N.nChords by rw [hnc]; exact B.hK)
      (Or.inl rfl)).1⟩
  have hA : SideAttach (interiorModel Q).W ((recOf x).toSet (interiorModel Q) Q) y.edge
      ((interiorModel Q).param Q y) := by
    rcases hy with rfl | rfl
    · exact hatt.1
    · exact hatt.2
  obtain ⟨a, b, harc, hcl⟩ := Restore.attach_closedArc hM hFam.2.1 hFam.1 hne
    (B.hregs.1.1 r hr) (chords_family B.hQ hcQ) hcS hcR hA
  obtain ⟨j, hj, hjr, hs, he⟩ := B.hregs.2.2.1.2.2.1 r hr a b harc
  refine ⟨j, (B.hregs.2.2.1.2.2.2 r hr j).2 ⟨hj, hjr⟩, hj, ?_⟩
  rw [hs, he]; exact hcl

/-- **The arc scan of an end of an emitted record finds a match.** -/
theorem scan_hex :
    ∃ j ∈ ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs,
      DrvD.matchB (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length j
        (DrvD.tA (interiorModel Q) Q (BuildNF.buildNF (interiorModel Q) Q L E) y j)
        (DrvD.tB (interiorModel Q) Q (BuildNF.buildNF (interiorModel Q) Q L E) y j) = true := by
  obtain ⟨j, hjm, hj, hcl⟩ := ends_on_arcs B hr hx hy
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; ram_grind
  exact ⟨j, hjm, DrvD.match_of_closedArc B.hK hE hj hcl (by simp [DrvD.tA]) (by simp [DrvD.tB])⟩

/-! ## The walk edges of an arc -/


end

/-- The number of walk edges `s.edge, s.edge + 1, …, e.edge` (cyclically) of an arc. -/
def arcCnt (n : ℕ) (a : ARec) : ℕ := (a.e.edge + n - a.s.edge) % n + 1

/-- The event positions of a valid list are on walk edges, with parameters in `[0, 1)`. -/
theorem evPos_ok (B : BaseCtx Q L E reg li) {m : ℕ} (hm : m < E.length) :
    (wposOf L (E.getD m 0)).edge < Q.n ∧ 0 ≤ (interiorModel Q).param Q (wposOf L (E.getD m 0)) ∧
      (interiorModel Q).param Q (wposOf L (E.getD m 0)) < 1 := by
  have hmem : E.getD m 0 ∈ E := by
    simp_all
  have hc : E.getD m 0 < 2 * L.length := by ram_grind
  obtain ⟨hp, h0, h1, -⟩ := BuildNF.attach_wposOf B.hL hc
  rw [show (interiorModel Q).W.n = Q.n from DownMath.walk_n Q] at hp
  simp_all

/-- The key of a position on a walk edge determines its edge. -/
theorem edge_of_key {M : Model} {Q : Polygon} {x : WPos} (h0 : 0 ≤ M.param Q x)
    (h1 : M.param Q x < 1) {w : ℕ} (hk : (w : ℝ) ≤ M.key Q x) (hk' : M.key Q x < w + 1) :
    x.edge = w := by
  unfold Model.key at hk hk'
  have a : (x.edge : ℝ) < w + 1 := by linarith
  have b : (w : ℝ) < x.edge + 1 := by linarith
  have a' : x.edge < w + 1 := by exact_mod_cast a
  have b' : w < x.edge + 1 := by exact_mod_cast b
  omega

section
variable (B : BaseCtx Q L E reg li)
include B
/-- **The last arc of `buildNF` starts and ends on distinct walk edges** (otherwise every event,
in particular both ends of the first chord, would lie on one walk edge). -/
theorem last_arc_edges :
    ((BuildNF.buildNF (interiorModel Q) Q L E).arc
        ((BuildNF.buildNF (interiorModel Q) Q L E).arcs.length - 1)).s.edge ≠
      ((BuildNF.buildNF (interiorModel Q) Q L E).arc
        ((BuildNF.buildNF (interiorModel Q) Q L E).arcs.length - 1)).e.edge := by
  set I := interiorModel Q with hI
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; ram_grind
  have hA := DrvD.arcs_length (M := I) (Q := Q) (E := E) B.hK
  obtain ⟨hA0, hlast⟩ := DrvD.gs_last (M := I) (Q := Q) (L := L) hE
  rw [hA]
  set j := (gapStarts I Q L E).length - 1 with hj
  have hs := DrvD.arc_s (M := I) (Q := Q) (E := E) B.hK (j := j) (by omega)
  have he := DrvD.arc_e (M := I) (Q := Q) (E := E) B.hK (j := j) (by omega)
  rw [hlast, Nat.sub_add_cancel hE, Nat.mod_self] at he
  rw [hlast] at hs
  rw [hs, he]
  intro hedge
  set w := (wposOf L (E.getD (E.length - 1) 0)).edge with hw
  obtain ⟨-, p00, p01⟩ := evPos_ok B hE
  obtain ⟨-, pl0, pl1⟩ := evPos_ok B (show E.length - 1 < E.length by omega)
  -- every event is on walk edge `w`
  have hall : ∀ m, m < E.length → (wposOf L (E.getD m 0)).edge = w := by
    intro m hm
    obtain ⟨-, q0, q1⟩ := evPos_ok B hm
    have k1 := DrvD.kE_mono B.hsort (Nat.zero_le m) hm
    have k2 := DrvD.kE_mono B.hsort (show m ≤ E.length - 1 by omega) (by omega)
    grind [Chazelle.Core.DrvB.edge_of_key, DrvD.kE, Model.key]
  -- the two ends of chord `0`
  have h0 : (0 : ℕ) ∈ E := B.hperm.mem_iff.2 (List.mem_range.2 (by ram_grind))
  have h1 : (1 : ℕ) ∈ E := B.hperm.mem_iff.2 (List.mem_range.2 (by ram_grind))
  obtain ⟨m0, hm0, e0⟩ := List.mem_iff_getElem.1 h0
  obtain ⟨m1, hm1, e1⟩ := List.mem_iff_getElem.1 h1
  have g0 : E.getD m0 0 = 0 := by
    ram_grind
  have g1 : E.getD m1 0 = 1 := by
    ram_grind
  have w0 := hall m0 hm0
  have w1 := hall m1 hm1
  rw [g0] at w0
  rw [g1] at w1
  rw [BuildNF.wposOf_even (by norm_num)] at w0
  rw [BuildNF.wposOf_odd (by norm_num)] at w1
  have hlt := BuildNF.pos_lt' (walkAx_interiorModel B.hQ) B.hL (i := 0) B.hK
  grind [CRec.lpos, CRec.rpos]

/-- **A position on a closed arc lies on one of the walk edges of the arc.** -/
theorem closedArc_range {j : ℕ}
    (hj : j < (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length) {p : ℕ} {t : ℝ} (hp : p < Q.n)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hc : Restore.ClosedArc ((interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s)
      ((interiorModel Q).key Q ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e) (p + t)) :
    ∃ u, u < arcCnt Q.n ((BuildNF.buildNF (interiorModel Q) Q L E).arc j) ∧
      (((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s.edge + u) % Q.n = p := by
  set I := interiorModel Q with hI
  set N := BuildNF.buildNF I Q L E with hN
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; ram_grind
  have hA := DrvD.arcs_length (M := I) (Q := Q) (E := E) B.hK
  rw [hN, hA] at hj
  obtain ⟨hA0, hlast⟩ := DrvD.gs_last (M := I) (Q := Q) (L := L) hE
  have hs := DrvD.arc_s (M := I) (Q := Q) (E := E) B.hK hj
  have he := DrvD.arc_e (M := I) (Q := Q) (E := E) B.hK hj
  obtain ⟨sn, s0, s1⟩ := evPos_ok B (DrvD.gs_lt_len hj)
  obtain ⟨en, e0, e1⟩ := evPos_ok B (Nat.mod_lt (DrvD.gs I Q L E j + 1) hE)
  rw [← hs] at sn s0 s1
  rw [← he] at en e0 e1
  set s := (N.arc j).s with hsd
  set e := (N.arc j).e with hed
  have ks : I.key Q s = s.edge + I.param Q s := rfl
  have ke : I.key Q e = e.edge + I.param Q e := rfl
  unfold arcCnt
  rw [← hsd, ← hed]
  
  by_cases hlt : j + 1 < (gapStarts I Q L E).length
  · -- an arc that does not wrap
    have hk := DrvD.key_s_lt_e (M := I) (Q := Q) B.hK hE hlt
    rw [← hN, ← hsd, ← hed] at hk
    have hin : I.key Q s ≤ p + t ∧ p + t ≤ I.key Q e := by
      rcases hc with hc | hc | hc
      · unfold sideInArc at hc; ram_grind
      all_goals ram_grind
    have h1 : s.edge ≤ p := by
      have : (s.edge : ℝ) < p + 1 := by linarith
      have : s.edge < p + 1 := by exact_mod_cast this
      omega
    have h2 : p ≤ e.edge := by
      have : (p : ℝ) < e.edge + 1 := by linarith
      have : p < e.edge + 1 := by exact_mod_cast this
      omega
    refine ⟨p - s.edge, ?_, ?_⟩
    · rw [show e.edge + Q.n - s.edge = (e.edge - s.edge) + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [show s.edge + (p - s.edge) = p by omega, Nat.mod_eq_of_lt hp]
  · -- the last arc wraps
    have hjl : j = (gapStarts I Q L E).length - 1 := by omega
    have hks := DrvD.key_s_last (M := I) (Q := Q) B.hK hE
    have hke := DrvD.key_e_last (M := I) (Q := Q) B.hK hE
    rw [← hN, ← hjl, ← hsd] at hks
    rw [← hN, ← hjl, ← hed] at hke
    have hge : I.key Q e ≤ I.key Q s := by
      rw [hks, hke]; exact DrvD.kE_mono B.hsort (Nat.zero_le _) (by omega)
    have hne := last_arc_edges B
    rw [← hN, hA, ← hjl, ← hsd, ← hed] at hne
    have hse : e.edge < s.edge := by
      have : (e.edge : ℝ) < s.edge + 1 := by linarith
      have : e.edge < s.edge + 1 := by exact_mod_cast this
      omega
    have hor : I.key Q s ≤ p + t ∨ p + t ≤ I.key Q e := by
      rcases hc with hc | hc | hc
      · unfold sideInArc at hc
        ram_grind
      all_goals ram_grind
    have hcnt : (e.edge + Q.n - s.edge) % Q.n = e.edge + Q.n - s.edge :=
      Nat.mod_eq_of_lt (by omega)
    rw [hcnt]
    rcases hor with h | h
    · have h1 : s.edge ≤ p := by
        have : (s.edge : ℝ) < p + 1 := by linarith
        have : s.edge < p + 1 := by exact_mod_cast this
        omega
      refine ⟨p - s.edge, by omega, ?_⟩
      rw [show s.edge + (p - s.edge) = p by omega, Nat.mod_eq_of_lt hp]
    · have h2 : p ≤ e.edge := by
        have : (p : ℝ) < e.edge + 1 := by linarith
        have : p < e.edge + 1 := by exact_mod_cast this
        omega
      refine ⟨p + Q.n - s.edge, by omega, ?_⟩
      rw [show s.edge + (p + Q.n - s.edge) = p + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hp]


end

end

end DrvB

end Chazelle.Core
