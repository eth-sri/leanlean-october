module

public import Chazelle.Core.DownPhaseDrvXSide
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Down phase, extraction (D6): X-R1, the kept test

For a chord record `ch` of the normal form `NR` of the region chain model, its chord `c` meets the
region `R` iff one of its two ends is at a regular position on the inner side of the chain walk
(`kept_iff`, the test `KeptT` of the RAM):

* an end at a regular inner position is a position of the host polygon `G` with a smaller sector,
  so the chord is attached to `G` and meets `R` (`meet_of_regIn`);
* conversely a kept chord is an interior chord of `G` (`adm_G`, from `ExtractOK`), attached to `G`
  at both ends; an end is then not on the box or the slit and not at a regular outer position
  (`end_ok`); and not both ends are at the chain ends `0`, `m` (the chord would be the chord gap
  edge of `G`, `not_both_irr`).
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set DownHost DownMath
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw IsHChordIn)
open Chazelle.Visibility (hseg)
open BuildNF (buildNF)
open DrvR (regHost)

/-- The height of a symbolic point. -/
theorem eval_snd (Q : Polygon) (s : SymPt) : (s.eval Q).2 = (Q.vtx (hidx s)).2 := by
  cases s <;> rfl

/-- Two attachments at the same point with disjoint sectors are impossible. -/
theorem attach_disj {W W' : Polygon} {y a b : ℝ} (hab : a < b) {p p' : ℕ} {t t' : ℝ}
    (h1 : SideAttach W (hseg y a b) p t) (h2 : SideAttach W' (hseg y a b) p' t')
    (hpt : sidePt W p t = sidePt W' p' t')
    (hdisj : ∀ x, sideLeft W p t x → ¬ sideLeft W' p' t' x) : False := by
  obtain ⟨-, -, -, hmem, r1, hr1, hs1⟩ := h1
  obtain ⟨-, -, -, -, r2, hr2, hs2⟩ := h2
  obtain ⟨x, hxc, hne, hxd⟩ := Extract.exists_near_mem hab hmem (lt_min hr1 hr2)
  exact hdisj x (hs1 x hxc hne (lt_of_lt_of_le hxd (min_le_left _ _)))
    (hs2 x hxc (hpt ▸ hne) (hpt ▸ lt_of_lt_of_le hxd (min_le_right _ _)))

/-- The right endpoint of a horizontal segment written as a segment of two points is one of
them. -/
theorem right_end_of_segment {a' b' : Point} {y a b : ℝ} (hab : a < b) (hy : a'.2 = b'.2)
    (h : hseg y a b = Chazelle.segment a' b') : ((b, y) : Point) = a' ∨ ((b, y) : Point) = b' := by
  rw [Visibility.segment_horizontal_eq_hseg hy] at h
  obtain ⟨h1, -, h2⟩ := Merge.hseg_inj hab.le h
  rcases le_total a'.1 b'.1 with hl | hl
  · right; rw [max_eq_right hl] at h2; exact Prod.ext h2 (h1.trans hy)
  · left; rw [max_eq_left hl] at h2; exact Prod.ext h2 h1

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF} {i0 g : ℕ}

set_option quotPrecheck false in
local notation "xS" => (buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
  (Qof P)
set_option quotPrecheck false in
local notation "xK" => nk (interiorModel (Qof P)) xS (reg r)
set_option quotPrecheck false in
local notation "xG" => hostPoly (Qof P) xS (reg r)
set_option quotPrecheck false in
local notation "xH" => regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r

namespace XCtx

variable (Y : XCtx P li L E reg r C NR i0 g)
include Y

/-- Host point `k` is the point of the host description. -/
theorem hpt_eval {k : ℕ} (hk : k < xK) : C.P.vtx k = (hpt (Qof P).n xH k).eval (Qof P) := by
  rw [Y.vtx_sig hk, hostPoly_vtx (sig_lt li (by have := Y.three; omega) _ _),
    rep_eval Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR Y.X.hli Y.X.hdh (sig_lt li (by have := Y.three; omega) _ _)
      (Y.hrep k hk)]

theorem hidx_lt {k : ℕ} (hkK : k < xK) : hidx (hpt (Qof P).n xH k) < (Qof P).n := by
  have hσ : sig li xK i0 k < xK := sig_lt li (by have := Y.three; omega) i0 k
  rcases Y.hrep k hkK with ⟨-, h⟩ | ⟨-, h', hh', -, (⟨-, -, h⟩ | ⟨-, h⟩)⟩ <;> rw [h]
  · exact ivB_lt li (by
      have hb := hostKeys_bounds (hk_mem (walkAx_interiorModel Y.X.hQ) Y.X.hFam.2.1 Y.X.hFam.1
        hσ)
      have : (⌊hk (interiorModel (Qof P)) xS (reg r) (sig li xK i0 k)⌋₊ : ℝ) <
          (interiorModel (Qof P)).W.n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
      rw [show (interiorModel (Qof P)).W.n = (Qof P).n from walk_n _] at this
      exact_mod_cast this)
  · exact hh'
  · exact hh'

/-- **The data of a chord record** of `NR`: a horizontal chord `hseg y A B` (`A < B`) at the height
of its vertex, attached at its two walk positions, whose points are its ends. -/
theorem chord_data {i : ℕ} (hi : i < NR.nChords) :
    ∃ A B : ℝ, A < B ∧
      (NR.chord i).toSet (chainModel C) (Qof P) = hseg ((Qof P).vtx (NR.chord i).h).2 A B ∧
      (NR.chord i).h < (Qof P).n ∧
      (NR.chord i).toSet (chainModel C) (Qof P) ∈ (chainModel C).Adm ∧
      SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx (NR.chord i).h).2 A B) (NR.chord i).lp
        ((chainModel C).param (Qof P) (NR.chord i).lpos) ∧
      SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx (NR.chord i).h).2 A B) (NR.chord i).rp
        ((chainModel C).param (Qof P) (NR.chord i).rpos) ∧
      sidePt (C.sideWalk C.sideBeta) (NR.chord i).lp
        ((chainModel C).param (Qof P) (NR.chord i).lpos) = ((A, ((Qof P).vtx (NR.chord i).h).2) : Point) ∧
      sidePt (C.sideWalk C.sideBeta) (NR.chord i).rp
        ((chainModel C).param (Qof P) (NR.chord i).rpos) = ((B, ((Qof P).vtx (NR.chord i).h).2) : Point) := by
  obtain ⟨hFam, -, hatt, -, -, -, -, -, -, hh, -⟩ := Y.X.hNR
  have hmemF : (NR.chord i).toSet (chainModel C) (Qof P) ∈ NR.F (chainModel C) (Qof P) :=
    ⟨NR.chord i, by unfold NF.chord; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi,
      rfl⟩
  have hadm := hFam.2.1 hmemF
  obtain ⟨y, a, b, hIC, -, hceq⟩ := hFam.2.1 hmemF
  set A := ((chainModel C).pos (Qof P) (NR.chord i).lpos).1 with hAdef
  set B := ((chainModel C).pos (Qof P) (NR.chord i).rpos).1 with hBdef
  have hc : (NR.chord i).toSet (chainModel C) (Qof P) = hseg ((Qof P).vtx (NR.chord i).h).2 A B := rfl
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hIC.lt.le (hceq.symm.trans hc)
  have hAB : A < B := by rw [← e2, ← e3]; exact hIC.lt
  obtain ⟨hl, hr⟩ := hatt i hi
  rw [hc] at hl hr
  have hpl : sidePt (C.sideWalk C.sideBeta) (NR.chord i).lp
      ((chainModel C).param (Qof P) (NR.chord i).lpos) = (chainModel C).pos (Qof P) (NR.chord i).lpos :=
    rfl
  have hpr : sidePt (C.sideWalk C.sideBeta) (NR.chord i).rp
      ((chainModel C).param (Qof P) (NR.chord i).rpos) = (chainModel C).pos (Qof P) (NR.chord i).rpos :=
    rfl
  refine ⟨A, B, hAB, hc, hh i hi, hadm, hl, hr, ?_, ?_⟩
  · have hm : sidePt (C.sideWalk C.sideBeta) (NR.chord i).lp
        ((chainModel C).param (Qof P) (NR.chord i).lpos) ∈ hseg ((Qof P).vtx (NR.chord i).h).2 A B :=
      hl.2.2.2.1
    exact Prod.ext rfl hm.1
  · have hm : sidePt (C.sideWalk C.sideBeta) (NR.chord i).rp
        ((chainModel C).param (Qof P) (NR.chord i).rpos) ∈ hseg ((Qof P).vtx (NR.chord i).h).2 A B :=
      hr.2.2.2.1
    exact Prod.ext rfl hm.1

/-- **The start-vertex test**: for an end attached at walk edge `p` of the tour (or up the slit),
`tZ` holds iff the parameter is `0`. -/
theorem tZ_iff {h : ℕ} (hh : h < (Qof P).n) {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx h).2 A B) p t) (h6 : 6 ≤ p)
    (hp : p ≤ 2 * C.m + 6) :
    tZ (Qof P).n xH C.m C.topIdx C.sideBeta h p ↔ t = 0 := by
  have hm := Y.hm
  have h3 := Y.three
  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  obtain ⟨-, ht0, ht1, hmem, rA, hrA, hsec⟩ := hat
  have hz : (sidePt (C.sideWalk C.sideBeta) p t).2 = ((Qof P).vtx h).2 := hmem.1
  have hheight : ((Qof P).vtx (hidx (hpt (Qof P).n xH (tK C.m C.topIdx C.sideBeta p)))).2 =
      (C.P.vtx (tK C.m C.topIdx C.sideBeta p)).2 := by
    rw [Y.hpt_eval (by omega), eval_snd]
  constructor
  · intro htz
    unfold tZ at htz
    rw [← htz] at hheight
    by_contra htne
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
    rcases lt_or_eq_of_le hp with hp' | hp'
    · -- inside a tour edge: the edge would be horizontal
      have hse := walk_sector_edge Y.cpSimple Y.X.hCs Y.X.hCm C.sideBeta h6 hp' ⟨ht0', ht1⟩
      have hv1 := walk_next Y.X.hCs Y.X.hCm C.sideBeta h6 hp'
      have hpt : sidePt (C.sideWalk C.sideBeta) p t = Chazelle.Geometry.lerp
          (C.P.vtx (tK C.m C.topIdx C.sideBeta p))
          (C.P.vtx (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m))
            (tK C.m C.topIdx C.sideBeta p))) t := by
        unfold sidePt; rw [hv0, hv1]
      rw [hpt, Chazelle.Geometry.lerp_snd, ← hheight] at hz
      have hflat : (C.P.vtx (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m))
          (tK C.m C.topIdx C.sideBeta p))).2 = (C.P.vtx (tK C.m C.topIdx C.sideBeta p)).2 := by
        have : t * ((C.P.vtx (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m))
            (tK C.m C.topIdx C.sideBeta p))).2 - ((Qof P).vtx h).2) = 0 := by
          linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 ht0'.ne'
        · linarith
      obtain ⟨x, hxc, hne, hxd⟩ := Extract.exists_near_mem hAB hmem hrA
      have hx := (hse x).1 (hsec x hxc hne hxd)
      have hxy : x.2 = ((Qof P).vtx h).2 := hxc.1
      unfold det at hx
      rw [hxy, hflat, ← hheight] at hx
      simp only [sub_self, mul_zero] at hx
      exact lt_irrefl _ hx
    · -- up the slit: above the top vertex
      subst hp'
      have hb := (C.sidePt_box C.sideBeta t).2.2.2.2.2.2
      rw [hb] at hz
      simp only at hz
      have hT : tK C.m C.topIdx C.sideBeta (2 * C.m + 6) = C.topIdx := by
        rw [← sideIdx_eq_tK]; exact C.sideIdx_two_m C.sideBeta
      rw [hT] at hheight
      have htop : C.top = C.P.vtx C.topIdx := by
        have := Y.X.hCm
        unfold Chain.top; exact chain_vertex_eq Y.X.hCs (by have := C.topIdx_le; omega)
      rw [← htop] at hheight
      have := C.top_snd_lt_radius
      nlinarith
  · intro ht
    subst ht
    rw [Chazelle.Chain.sidePt_zero, hv0] at hz
    unfold tZ
    by_contra hne
    exact Y.X.hdh _ _ hh (Y.hidx_lt (by omega)) hne (by rw [← hz, hheight])

/-- **An end at a regular inner position: the chord meets `R`.** -/
theorem meet_of_regIn {h : ℕ} (hh : h < (Qof P).n) {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx h).2 A B) p t)
    (hreg : RegIn (Qof P).n xH li C.m C.topIdx C.sideBeta h p) :
    (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty := by
  have hm := Y.hm
  have h3 := Y.three
  have hm1 := C.one_le
  obtain ⟨h6, hp, hlast, hirr, hside⟩ := hreg
  have hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = li := by
    cases li <;> simp_all
  have htz := Y.tZ_iff hh hAB hat h6 hp
  have ht0 := hat.2.1
  have ht1 := hat.2.2.1
  have hcs : ∃ y a b : ℝ, a < b ∧ hseg ((Qof P).vtx h).2 A B = hseg y a b := ⟨_, A, B, hAB, rfl⟩
  rcases ht0.lt_or_eq with ht0' | ht0'
  · have hp' : p < 2 * C.m + 6 := by
      rcases lt_or_eq_of_le hp with h' | h'
      · exact h'
      · exact absurd (htz.1 (hlast h')) ht0'.ne'
    obtain ⟨hpt, hsec⟩ := Y.inner_edge h6 hp' ⟨ht0', ht1⟩ hA
    exact meet_of_attach Y hcs (ExtG.attach_of_sector hpt.symm (fun x hx => (hsec x).1 hx)
      (by rw [Y.gn]; exact sig_lt li (by omega) _ _) ht0 ht1 hat)
  · subst ht0'
    have hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0 := fun h0 =>
      hirr ⟨htz.2 rfl, Or.inl ((tK_eq_zero_iff _ hm1 p).2 h0)⟩
    have hum : tU C.m C.topIdx C.sideBeta p ≠ C.m := fun h0 =>
      hirr ⟨htz.2 rfl, Or.inr ((tK_eq_m_iff _ hm1 p).2 h0)⟩
    obtain ⟨hpt, hsec⟩ := Y.inner_vtx h6 hp hu0 hum hA
    exact meet_of_attach Y hcs (ExtG.attach_of_sector hpt.symm hsec
      (by rw [Y.gn]; exact sig_lt li (by omega) _ _) le_rfl one_pos hat)

/-- **A kept chord is an interior chord of the host polygon.** -/
theorem adm_G {c : Set Point} (hc : c ∈ (chainModel C).Adm) (hk : (c ∩ reg r).Nonempty) :
    c ∈ (interiorModel xG).Adm := by
  obtain ⟨hI, hsub⟩ := Y.hext.loc (F₁ := {c}) (by simpa using hc) c ⟨rfl, hk⟩
  obtain ⟨y, a, b, hIC, rfl⟩ := hI
  have hReq := DownDrv.region_eq_intHost Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
  have hRD : reg r ⊆ (interiorModel (Qof P)).D := fun z hz =>
    (Chazelle.Chain.regionsIn_subset Y.X.hR hz).1
  refine ⟨y, a, b, ⟨hIC.lt, fun h => hIC.left_not (hRD (hReq ▸ h)),
    fun h => hIC.right_not (hRD (hReq ▸ h)), fun x hxa hxb => ?_⟩, rfl⟩
  rw [← hReq]
  exact hsub ⟨⟨rfl, hxa.le, hxb.le⟩, hIC.open_mem x hxa hxb⟩

/-- The ends of a kept chord are attached to the host polygon. -/
theorem kept_ends {h : ℕ} {A B : ℝ} (hAB : A < B)
    (hc : hseg ((Qof P).vtx h).2 A B ∈ (chainModel C).Adm)
    (hk : (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty) :
    (∃ q s, SideAttach xG (hseg ((Qof P).vtx h).2 A B) q s ∧
        sidePt xG q s = ((A, ((Qof P).vtx h).2) : Point)) ∧
      ∃ q s, SideAttach xG (hseg ((Qof P).vtx h).2 A B) q s ∧
        sidePt xG q s = ((B, ((Qof P).vtx h).2) : Point) := by
  have hadm := Y.adm_G hc hk
  have hMH : WalkAx (interiorModel xG) := walkAx_interiorModel Y.gSimple
  have hW : (interiorModel xG).W = xG :=
    DownDrv.interiorWalk_hostPoly Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
  obtain ⟨a', b', -, hseg', hy, -, hEa, hEb⟩ := hMH.ends _ hadm
  rw [hW] at hEa hEb
  refine ⟨?_, ?_⟩
  · rcases DownDrv.left_end_of_segment hAB hy hseg' with e | e
    · obtain ⟨q, s, h1, h2⟩ := hEa.1; exact ⟨q, s, h1, h2.trans e.symm⟩
    · obtain ⟨q, s, h1, h2⟩ := hEb.1; exact ⟨q, s, h1, h2.trans e.symm⟩
  · rcases right_end_of_segment hAB hy hseg' with e | e
    · obtain ⟨q, s, h1, h2⟩ := hEa.1; exact ⟨q, s, h1, h2.trans e.symm⟩
    · obtain ⟨q, s, h1, h2⟩ := hEb.1; exact ⟨q, s, h1, h2.trans e.symm⟩

/-- **An end of a kept chord** is on the tour (not on the box or the slit above the top vertex),
and if it is at a regular position, that position is on the inner side. -/
theorem end_ok {h : ℕ} {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx h).2 A B) p t) {q : ℕ} {s : ℝ}
    (hG : SideAttach xG (hseg ((Qof P).vtx h).2 A B) q s)
    (hpt : sidePt xG q s = sidePt (C.sideWalk C.sideBeta) p t) :
    6 ≤ p ∧ p ≤ 2 * C.m + 6 ∧ (p = 2 * C.m + 6 → t = 0) ∧
      (¬ (t = 0 ∧ (tU C.m C.topIdx C.sideBeta p = 0 ∨ tU C.m C.topIdx C.sideBeta p = C.m)) →
        decide (tU C.m C.topIdx C.sideBeta p < C.m) = li) := by
  have hm := Y.hm
  have h3 := Y.three
  have ⟨hpW, ht0, ht1, _⟩ := hat
  have ⟨hqG, hs0, hs1, _⟩ := hG
  rw [Y.gn] at hqG
  rw [C.sideWalk_n] at hpW
  have hbox : ¬ (p ≤ 5 ∨ (p = 2 * C.m + 6 ∧ 0 < t)) := fun hb =>
    Y.box_ne ht0 ht1 hb hqG hs0 hs1 hpt
  have h6 : 6 ≤ p := by omega
  have hp : p ≤ 2 * C.m + 6 := by omega
  have hlast : p = 2 * C.m + 6 → t = 0 := fun h' => by
    by_contra hne; exact hbox (Or.inr ⟨h', lt_of_le_of_ne ht0 (Ne.symm hne)⟩)
  refine ⟨h6, hp, hlast, fun hreg => ?_⟩
  by_contra hside
  have hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = !li := by
    generalize decide (tU C.m C.topIdx C.sideBeta p < C.m) = d at hside ⊢
    cases li <;> cases d <;> simp_all
  have hGn  := Y.gn
  rcases ht0.lt_or_eq with ht0' | ht0'
  · have hp' : p < 2 * C.m + 6 := by
      rcases lt_or_eq_of_le hp with h' | h'
      · exact h'
      · exact absurd (hlast h') ht0'.ne'
    obtain ⟨hpt', hsec⟩ := Y.outer_edge h6 hp' ⟨ht0', ht1⟩ hA
    obtain ⟨hq, hs⟩ := FactsInterior.pos_unique Y.gSimple (by rwx [hGn])
      (by rw [hGn]; exact sig_lt li (by omega) _ _) hs0 hs1 (by linarith) (by linarith)
      (hpt.trans hpt')
    subst hq hs
    exact attach_disj hAB hat hG hpt' hsec
  · subst ht0'
    have hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0 := fun h0 => hreg ⟨rfl, Or.inl h0⟩
    have hum : tU C.m C.topIdx C.sideBeta p ≠ C.m := fun h0 => hreg ⟨rfl, Or.inr h0⟩
    obtain ⟨hpt', hsec⟩ := Y.outer_vtx h6 hp hu0 hum hA
    obtain ⟨hq, hs⟩ := FactsInterior.pos_unique Y.gSimple (by rwx [hGn])
      (by rw [hGn]; exact sig_lt li (by omega) _ _) hs0 hs1 le_rfl one_pos (hpt.trans hpt')
    subst hq hs
    exact attach_disj hAB hat hG hpt' hsec

/-- The chain ends are the ends of the chord gap edge of `G`. -/
theorem sig_ends : (sig li xK i0 0 = g ∧ sig li xK i0 C.m = (g + 1) % xK) ∨
    (sig li xK i0 0 = (g + 1) % xK ∧ sig li xK i0 C.m = g) := by
  have hm := Y.hm
  have h3 := Y.three
  have hgi := Y.hgi
  have hg := Y.hg
  have e1 : (i0 + (xK - 1)) % xK = g := by
    rw [← Nat.mod_add_mod, ← hgi, Nat.mod_add_mod, show g + 1 + (xK - 1) = g + xK by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hg]
  have e2 : (i0 + 0) % xK = (g + 1) % xK := by rw [add_zero, hgi]
  unfold sig rho
  cases li
  · left; simp only [Bool.false_eq_true, ite_false]
    rw [Nat.sub_zero, e1, hm, show xK - 1 - (xK - 1) = 0 by omega, e2]; exact ⟨rfl, rfl⟩
  · right; simp only [ite_true]
    rw [e2, hm, e1]; exact ⟨rfl, rfl⟩

/-- **Not both ends of a kept chord are at the chain ends.** -/
theorem not_both_irr {h : ℕ} {A B : ℝ} (hAB : A < B)
    (hc : hseg ((Qof P).vtx h).2 A B ∈ (chainModel C).Adm)
    (hk : (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty)
    {kL kR : ℕ} (hL : kL = 0 ∨ kL = C.m) (hR : kR = 0 ∨ kR = C.m)
    (hzL : C.P.vtx kL = ((A, ((Qof P).vtx h).2) : Point))
    (hzR : C.P.vtx kR = ((B, ((Qof P).vtx h).2) : Point)) : False := by
  have hm := Y.hm
  have h3 := Y.three
  have hadm := Y.adm_G hc hk
  obtain ⟨y', a', b', hIC, heq⟩ := hadm
  obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hAB.le heq
  -- the two ends are the two ends of the chord gap edge
  have hne : kL ≠ kR := by
    intro e; rw [e, hzR] at hzL
    have := congrArg Prod.fst hzL; sil at this
  have hends : (C.P.vtx kL = (xG).vtx g ∧ C.P.vtx kR = (xG).vtx ((g + 1) % xK)) ∨
      (C.P.vtx kL = (xG).vtx ((g + 1) % xK) ∧ C.P.vtx kR = (xG).vtx g) := by
    rw [Y.vtx_sig (by omega), Y.vtx_sig (by omega)]
    rcases Y.sig_ends with ⟨e0, em⟩ | ⟨e0, em⟩ <;> rcases hL with rfl | rfl <;>
      rcases hR with rfl | rfl <;> simp_all
  have hedge : ∀ x : ℝ, A < x → x < B →
      ((x, ((Qof P).vtx h).2) : Point) ∈ (xG).boundary := by
    intro x hxa hxb
    refine ⟨g, by rw [Y.gn]; exact Y.hg, ?_⟩
    unfold Polygon.edge
    rw [Y.gn]
    have hmem : ((x, ((Qof P).vtx h).2) : Point) ∈ Chazelle.segment (C.P.vtx kL) (C.P.vtx kR) := by
      rw [hzL, hzR, Visibility.segment_horizontal_eq_hseg
        (a := ((A, ((Qof P).vtx h).2) : Point)) (b := ((B, ((Qof P).vtx h).2) : Point)) rfl]
      simp only [min_eq_left hAB.le, max_eq_right hAB.le]
      exact ⟨rfl, hxa.le, hxb.le⟩
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rwa [e1, e2] at hmem
    · rw [e1, e2] at hmem; rwa [Chazelle.Geometry.segment_comm]
  have hmid := hIC.open_mem ((A + B) / 2) (by linarith) (by linarith)
  exact hmid.2 (hedge _ (by linarith) (by linarith))

/-- **X-R1: the kept test.**  The chord of record `i` of `NR` meets the region iff one of its ends
is at a regular position on the inner side. -/
theorem kept_iff {i : ℕ} (hi : i < NR.nChords) :
    KeptT (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp (NR.chord i).rp ↔
      ((NR.chord i).toSet (chainModel C) (Qof P) ∩ reg r).Nonempty := by
  have hm1 := C.one_le
  obtain ⟨A, B, hAB, hc, hh, hadm, hl, hr, hzl, hzr⟩ := Y.chord_data hi
  rw [hc]
  constructor
  · rintro (hreg | hreg)
    · exact Y.meet_of_regIn hh hAB hl hreg
    · exact Y.meet_of_regIn hh hAB hr hreg
  · intro hk
    obtain ⟨⟨qL, sL, hGL, hzGL⟩, ⟨qR, sR, hGR, hzGR⟩⟩ := Y.kept_ends hAB (hc ▸ hadm) hk
    obtain ⟨h6L, hpL, hlastL, hsideL⟩ := Y.end_ok hAB hl hGL (hzGL.trans hzl.symm)
    obtain ⟨h6R, hpR, hlastR, hsideR⟩ := Y.end_ok hAB hr hGR (hzGR.trans hzr.symm)
    have htzL := Y.tZ_iff hh hAB hl h6L hpL
    have htzR := Y.tZ_iff hh hAB hr h6R hpR
    -- a regular end gives the test
    have hreg : ∀ {p : ℕ} {t : ℝ}, 6 ≤ p → p ≤ 2 * C.m + 6 → (p = 2 * C.m + 6 → t = 0) →
        (tZ (Qof P).n xH C.m C.topIdx C.sideBeta (NR.chord i).h p ↔ t = 0) →
        ¬ (t = 0 ∧ (tU C.m C.topIdx C.sideBeta p = 0 ∨ tU C.m C.topIdx C.sideBeta p = C.m)) →
        decide (tU C.m C.topIdx C.sideBeta p < C.m) = li →
        RegIn (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h p := by
      intro p t h6 hp hlast htz hirr hside
      refine ⟨h6, hp, fun h' => htz.2 (hlast h'), fun ⟨hz, hk0⟩ => hirr ⟨htz.1 hz, ?_⟩, ?_⟩
      · rcases hk0 with h0 | h0
        · exact Or.inl ((tK_eq_zero_iff _ hm1 p).1 h0)
        · exact Or.inr ((tK_eq_m_iff _ hm1 p).1 h0)
      · rws [← hside]
    by_cases hirrL : (chainModel C).param (Qof P) (NR.chord i).lpos = 0 ∧
        (tU C.m C.topIdx C.sideBeta (NR.chord i).lp = 0 ∨
          tU C.m C.topIdx C.sideBeta (NR.chord i).lp = C.m)
    · by_cases hirrR : (chainModel C).param (Qof P) (NR.chord i).rpos = 0 ∧
          (tU C.m C.topIdx C.sideBeta (NR.chord i).rp = 0 ∨
            tU C.m C.topIdx C.sideBeta (NR.chord i).rp = C.m)
      · exfalso
        have hkL : tK C.m C.topIdx C.sideBeta (NR.chord i).lp = 0 ∨
            tK C.m C.topIdx C.sideBeta (NR.chord i).lp = C.m := by
          rcases hirrL.2 with h0 | h0
          · exact Or.inl ((tK_eq_zero_iff _ hm1 _).2 h0)
          · exact Or.inr ((tK_eq_m_iff _ hm1 _).2 h0)
        have hkR : tK C.m C.topIdx C.sideBeta (NR.chord i).rp = 0 ∨
            tK C.m C.topIdx C.sideBeta (NR.chord i).rp = C.m := by
          rcases hirrR.2 with h0 | h0
          · exact Or.inl ((tK_eq_zero_iff _ hm1 _).2 h0)
          · exact Or.inr ((tK_eq_m_iff _ hm1 _).2 h0)
        refine Y.not_both_irr hAB (hc ▸ hadm) hk hkL hkR ?_ ?_
        · rw [← walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6L hpL, ← hzl, hirrL.1,
            Chazelle.Chain.sidePt_zero]
        · rw [← walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6R hpR, ← hzr, hirrR.1,
            Chazelle.Chain.sidePt_zero]
      · exact Or.inr (hreg h6R hpR hlastR htzR hirrR (hsideR hirrR))
    · exact Or.inl (hreg h6L hpL hlastL htzL hirrL (hsideL hirrL))

end XCtx

end

end

end DrvX

end Chazelle.Core
