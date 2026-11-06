module
public import Chazelle.MacT

public import Chazelle.Core.DownPhaseDrvXSide

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
    (h1 : SideAttach W ztbiq p t) (h2 : SideAttach W' ztbiq p' t')
    (hpt : sidePt W p t = sidePt W' p' t')
    (hdisj : ∀ x, sideLeft W p t x → ¬ sideLeft W' p' t' x) : False := by
  obtain ⟨-, -, -, hmem, r1, hr1, hs1⟩ := h1
  obtain ⟨-, -, -, -, r2, hr2, hs2⟩ := h2
  obtain ⟨x, hxc, hne, hxd⟩ := Extract.exists_near_mem hab hmem zttss
  grind

/-- The right endpoint of a horizontal segment written as a segment of two points is one of
them. -/
theorem right_end_of_segment {a' b' : Point} {y a b : ℝ} (hab : a < b) (hy : a'.2 = b'.2)
    (h : hseg y a b = Chazelle.segment a' b') : (ztdy : Point) = a' ∨ (ztdy : Point) = b' := by
  zujhh
  obtain ⟨h1, -, h2⟩ := Merge.hseg_inj hab.le h
  grind

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF} {i0 g : ℕ}

set_option quotPrecheck false in
local notation "xS" => (buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
  zta
set_option quotPrecheck false in
local notation "xK" => nk (interiorModel (Qof P)) xS (reg r)
set_option quotPrecheck false in
local notation "xG" => hostPoly (Qof P) xS (reg r)
set_option quotPrecheck false in
local notation "xH" => regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r

namespace XCtx

variable (Y : XCtx P li L E reg r C NR i0 g)
include Y

variable {k : ℕ} {i : ℕ} {h : ℕ} {A B : ℝ}
/-- Host point `k` is the point of the host description. -/
theorem hpt_eval (hk : k < xK) : C.P.vtx k = (hpt (Qof P).n xH k).eval zta := by
  rw [Y.vtx_sig hk, hostPoly_vtx ztqwj,
    rep_eval Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR Y.X.hli Y.X.hdh ztqwj
      (Y.hrep k hk)]

theorem hidx_lt (hkK : k < xK) : hidx (hpt (Qof P).n xH k) < (Qof P).n := by
  have hσ : sig li xK i0 k < xK := sig_lt li by_omega i0 k
  rcases Y.hrep k hkK with ⟨-, h⟩ | ⟨-, h', hh', -, (⟨-, -, h⟩ | ⟨-, h⟩)⟩ <;> zvmwc
  · exact ivB_lt li (by
      have hb := hostKeys_bounds (hk_mem (walkAx_interiorModel Y.X.hQ) Y.X.hFam.2.1 Y.X.hFam.1
        hσ)
      zuepf
      rw [show (interiorModel zta).W.n = (Qof P).n from walk_n _] at this
      exact_mod_cast this)
  · tauto
  tauto

/-- **The data of a chord record** of `NR`: a horizontal chord `hseg y A B` (`A < B`) at the height
of its vertex, attached at its two walk positions, whose points are its ends. -/
theorem chord_data (hi : i < NR.nChords) :
    ∃ A B : ℝ, A < B ∧
      (NR.chord i).toSet ztc zta = hseg ((Qof P).vtx (NR.chord i).h).2 A B ∧
      (NR.chord i).h < (Qof P).n ∧
      (NR.chord i).toSet ztc zta ∈ (chainModel C).Adm ∧
      SideAttach ztcs ztgrn (NR.chord i).lp
        ztxts ∧
      SideAttach ztcs ztgrn (NR.chord i).rp
        ztxtt ∧
      sidePt ztcs (NR.chord i).lp
        ztxts = ((A, ((Qof P).vtx (NR.chord i).h).2) : Point) ∧
      sidePt ztcs (NR.chord i).rp
        ztxtt = ((B, ((Qof P).vtx (NR.chord i).h).2) : Point) := by
  obtain ⟨hFam, -, hatt, -, -, -, -, -, -, hh, -⟩ := Y.X.hNR
  have hmemF : (NR.chord i).toSet _ _ ∈ NR.F ztc zta :=
    ⟨NR.chord i, by unfold NF.chord; rw [List.getD_eq_getElem _ _ hi]; grind,
      rfl⟩
  have hadm := hFam.2.1 hmemF
  obtain ⟨y, a, b, hIC, -, hceq⟩ := hFam.2.1 hmemF
  set A := ((chainModel C).pos zta (NR.chord i).lpos).1 with hAdef
  set B := ((chainModel C).pos zta (NR.chord i).rpos).1 with hBdef
  have hc : (NR.chord i).toSet _ _ = hseg ((Qof P).vtx (NR.chord i).h).2 A B := rfl
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hIC.lt.le (hceq.symm.trans hc)
  have hAB : A < B := by rw [← e2, ← e3]; exact hIC.lt
  obtain ⟨hl, hr⟩ := hatt i hi
  zvnmd at hl hr
  have hpl : sidePt ztcs (NR.chord i).lp
      _ = (chainModel C).pos zta (NR.chord i).lpos :=
    rfl
  have hpr : sidePt ztcs (NR.chord i).rp
      _ = (chainModel C).pos zta (NR.chord i).rpos :=
    rfl
  refine ⟨A, B, hAB, hc, by_simp_all, hadm, hl, hr, ?_, ?_⟩
  · have hm : sidePt _ (NR.chord i).lp
        _ ∈ hseg ((Qof P).vtx (NR.chord i).h).2 A B :=
      hl.2.2.2.1
    zulxh
  · have hm : sidePt _ (NR.chord i).rp
        _ ∈ hseg ((Qof P).vtx (NR.chord i).h).2 A B :=
      hr.2.2.2.1
    zulxh

/-- **The start-vertex test**: for an end attached at walk edge `p` of the tour (or up the slit),
`tZ` holds iff the parameter is `0`. -/
theorem tZ_iff (hh : h < (Qof P).n) {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach ztcs ztwu p t) (h6 : 6 ≤ p)
    (hp : p ≤ 2 * C.m + 6) :
    tZ (Qof P).n xH C.m C.topIdx C.sideBeta h p ↔ t = 0 := by
  zukj

  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  zuhfr
  obtain ⟨-, ht0, ht1, hmem, rA, hrA, hsec⟩ := hat
  have hz : (sidePt _ p t).2 = ((Qof P).vtx h).2 := hmem.1
  have hheight : ((Qof P).vtx (hidx (hpt (Qof P).n xH ztqn))).2 =
      (C.P.vtx ztqn).2 := by
    rw [Y.hpt_eval by_omega, eval_snd]
  constructor
  · intro htz
    unfold tZ at htz
    rw [← htz] at hheight
    by_contra htne
    have ht0' : ztfkp := by_grind
    zujdy
    · -- inside a tour edge: the edge would be horizontal
      have hse := walk_sector_edge Y.cpSimple Y.X.hCs Y.X.hCm C.sideBeta h6 hp' ztkls
      have hv1 := walk_next Y.X.hCs Y.X.hCm C.sideBeta h6 hp'
      have hpt : sidePt ztcs p t = Chazelle.Geometry.lerp
          ztbadx
          (C.P.vtx (kNext ztxgq
            ztqn)) t := by
        zuhbc
      rw [hpt, Chazelle.Geometry.lerp_snd, ← hheight] at hz
      have hflat : (C.P.vtx (kNext ztxgq
          ztqn)).2 = (C.P.vtx (tK C.m C.topIdx C.sideBeta p)).2 := by
        grind
      obtain ⟨x, hxc, hne, hxd⟩ := Extract.exists_near_mem hAB hmem hrA
      have hx := (hse x).1 by_grind
      have hxy := hxc.1
      zumsi
      rw [hxy, hflat, ← hheight] at hx
      grind
    · -- up the slit: above the top vertex
      subst hp'
      have hb := (C.sidePt_box C.sideBeta t).2.2.2.2.2.2
      rw [hb] at hz
      simp only at hz
      have hT : tK C.m C.topIdx C.sideBeta ztcc = C.topIdx := by
        zuorj; exact C.sideIdx_two_m C.sideBeta
      zvncs at hheight
      have htop : C.top = C.P.vtx C.topIdx := by
        have := Y.X.hCm
        unfold Chain.top; exact chain_vertex_eq Y.X.hCs by_omega
      rw [← htop] at hheight
      have := C.top_snd_lt_radius
      nlinarith
  · zuibv
    zucfb
    rw [Chazelle.Chain.sidePt_zero, hv0] at hz
    unfold tZ
    zuct
    exact Y.X.hdh _ _ hh (Y.hidx_lt by_omega) hne by_simp_all

/-- **An end at a regular inner position: the chord meets `R`.** -/
theorem meet_of_regIn (hh : h < (Qof P).n) {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach ztcs ztwu p t)
    (hreg : RegIn (Qof P).n xH li C.m C.topIdx C.sideBeta h p) :
    (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty := by
  zukj

  zubb
  obtain ⟨h6, hp, hlast, hirr, hside⟩ := hreg
  have hA : decide ztpi = li := by
    simp_all
  have htz := Y.tZ_iff hh hAB hat h6 hp
  zuiam

  have hcs : ∃ y a b : ℝ, a < b ∧ hseg ((Qof P).vtx h).2 A B = hseg y a b := by_grind
  zucox
  · have hp' : ztjaa := by
      grind
    obtain ⟨hpt, hsec⟩ := Y.inner_edge h6 hp' ztkls hA
    exact meet_of_attach Y hcs (ExtG.attach_of_sector hpt.symm by_simp_all
      ztcpl ht0 ht1 hat)
  · zultg
    have hu0 := fun h0 =>
      hirr ⟨htz.2 rfl, Or.inl ((tK_eq_zero_iff _ hm1 p).2 h0)⟩
    have hum := fun h0 =>
      hirr ⟨htz.2 rfl, Or.inr ((tK_eq_m_iff _ hm1 p).2 h0)⟩
    obtain ⟨hpt, hsec⟩ := Y.inner_vtx h6 hp hu0 hum hA
    exact meet_of_attach Y hcs (ExtG.attach_of_sector hpt.symm hsec
      ztcpl le_rfl one_pos hat)

/-- **A kept chord is an interior chord of the host polygon.** -/
theorem adm_G {c : Set Point} (hc : c ∈ (chainModel C).Adm) (hk : (c ∩ reg r).Nonempty) :
    c ∈ (interiorModel xG).Adm := by
  obtain ⟨hI, hsub⟩ := Y.hext.loc (F₁ := {c}) by_simp_all c ⟨rfl, hk⟩
  obtain ⟨y, a, b, hIC, rfl⟩ := hI
  zuhxj
  have hRD : reg r ⊆ (interiorModel _).D := fun z hz =>
    (Chazelle.Chain.regionsIn_subset Y.X.hR hz).1
  refine ⟨y, a, b, ⟨hIC.lt, fun h => hIC.left_not ztvtr,
    fun h => hIC.right_not ztvtr, fun x hxa hxb => ?_⟩, rfl⟩
  zulqy
  exact hsub ⟨ztref, hIC.open_mem x hxa hxb⟩

/-- The ends of a kept chord are attached to the host polygon. -/
theorem kept_ends (hAB : A < B)
    (hc : hseg ((Qof P).vtx h).2 A B ∈ (chainModel C).Adm)
    (hk : (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty) :
    (∃ q s, SideAttach xG ztwu q s ∧
        sidePt xG q s = (ztelp : Point)) ∧
      ∃ q s, SideAttach xG ztwu q s ∧
        sidePt xG q s = (ztelx : Point) := by
  zukay
  have hMH : ztezg := walkAx_interiorModel Y.gSimple
  have hW : (interiorModel xG).W = xG :=
    DownDrv.interiorWalk_hostPoly Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
  obtain ⟨a', b', -, hseg', hy, -, hEa, hEb⟩ := hMH.ends _ hadm
  rw [hW] at hEa hEb
  zujx
  · rcases DownDrv.left_end_of_segment hAB hy hseg' with e | e
    · zueje
    · zuejf
  · rcases right_end_of_segment hAB hy hseg' with e | e
    · zueje
    · zuejf

/-- **An end of a kept chord** is on the tour (not on the box or the slit above the top vertex),
and if it is at a regular position, that position is on the inner side. -/
theorem end_ok (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach ztcs ztwu p t) {q : ℕ} {s : ℝ}
    (hG : SideAttach xG ztwu q s)
    (hpt : sidePt xG q s = sidePt ztcs p t) :
    6 ≤ p ∧ p ≤ 2 * C.m + 6 ∧ ztkbx ∧
      (¬ ztfcm →
        decide ztpi = li) := by
  zukj

  have ⟨hpW, ht0, ht1, _⟩ := hat
  have ⟨hqG, hs0, hs1, _⟩ := hG
  rw [Y.gn] at hqG
  rw [C.sideWalk_n] at hpW
  have hbox : ¬ ztzgr := fun hb =>
    Y.box_ne ht0 ht1 hb hqG hs0 hs1 hpt
  have h6 : ztsaj := by_omega
  have hp : p ≤ 2 * C.m + 6 := by_omega
  have hlast : p = 2 * C.m + 6 → t = 0 := fun h' => by
    grind
  refine ⟨h6, hp, hlast, fun hreg => ?_⟩
  by_contra hside
  have hA : decide ztpi = !li := by
    grind
  zumbt
  zucox
  · have hp' : ztjaa := by
      grind
    obtain ⟨hpt', hsec⟩ := Y.outer_edge h6 hp' ztkls hA
    obtain ⟨hq, hs⟩ := FactsInterior.pos_unique Y.gSimple by_omega
      ztirp hs0 hs1 by_linarith by_linarith
      ztvwb
    zugzw

  · zultg
    have hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0 := by_grind
    have hum : tU C.m C.topIdx C.sideBeta p ≠ C.m := by_grind
    obtain ⟨hpt', hsec⟩ := Y.outer_vtx h6 hp hu0 hum hA
    obtain ⟨hq, hs⟩ := FactsInterior.pos_unique Y.gSimple by_omega
      ztirp hs0 hs1 le_rfl one_pos ztvwb
    zugzw

/-- The chain ends are the ends of the chord gap edge of `G`. -/
theorem sig_ends : (sig li xK i0 0 = g ∧ sig li xK i0 C.m = ztbs % xK) ∨
    (sig li xK i0 0 = ztbs % xK ∧ sig li xK i0 C.m = g) := by
  zukj

  have hgi := Y.hgi
  have hg := Y.hg
  have e1 : (i0 + (xK - 1)) % xK = g := by
    rw [← Nat.mod_add_mod, ← hgi, Nat.mod_add_mod, show g + 1 + (xK - 1) = g + xK by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hg]
  have e2 : (i0 + 0) % xK = ztbs % xK := by_simp_all
  unfold sig rho
  grind

/-- **Not both ends of a kept chord are at the chain ends.** -/
theorem not_both_irr (hAB : A < B)
    (hc : hseg ((Qof P).vtx h).2 A B ∈ (chainModel C).Adm)
    (hk : (hseg ((Qof P).vtx h).2 A B ∩ reg r).Nonempty)
    {kL kR : ℕ} (hL : kL = 0 ∨ kL = C.m) (hR : kR = 0 ∨ kR = C.m)
    (hzL : C.P.vtx kL = (ztelp : Point))
    (hzR : C.P.vtx kR = (ztelx : Point)) : False := by
  zukj

  zukay
  obtain ⟨y', a', b', hIC, heq⟩ := hadm
  obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hAB.le heq
  -- the two ends are the two ends of the chord gap edge
  have hne : kL ≠ kR := by
    grind
  have hends : (C.P.vtx kL = (xG).vtx g ∧ C.P.vtx kR = (xG).vtx ((g + 1) % xK)) ∨
      (C.P.vtx kL = (xG).vtx ((g + 1) % xK) ∧ C.P.vtx kR = (xG).vtx g) := by
    rw [Y.vtx_sig by_omega, Y.vtx_sig by_omega]
    rcases Y.sig_ends with ⟨e0, em⟩ | ⟨e0, em⟩ <;> rcases hL with rfl | rfl <;>
      rcases hR with rfl | rfl <;> simp_all
  have hedge : ∀ x : ℝ, A < x → x < B →
      (ztkhb : Point) ∈ (xG).boundary := by
    intro x hxa hxb
    refine ⟨g, by rw [Y.gn]; exact Y.hg, ?_⟩
    zucrd
    rw [Y.gn]
    have hmem : (ztkhb : Point) ∈ Chazelle.segment (C.P.vtx kL) (C.P.vtx kR) := by
      rw [hzL, hzR, Visibility.segment_horizontal_eq_hseg
        (a := (ztelp : Point)) (b := (ztelx : Point)) rfl]
      simp only [min_eq_left hAB.le, max_eq_right hAB.le]
      exact ztref
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp_all
    · rw [e1, e2] at hmem; rwa [Chazelle.Geometry.segment_comm]
  have hmid := hIC.open_mem ((A + B) / 2) by_linarith by_linarith
  grind

/-- **X-R1: the kept test.**  The chord of record `i` of `NR` meets the region iff one of its ends
is at a regular position on the inner side. -/
theorem kept_iff (hi : i < NR.nChords) :
    KeptT (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp (NR.chord i).rp ↔
      ((NR.chord i).toSet ztc zta ∩ reg r).Nonempty := by
  zubb
  obtain ⟨A, B, hAB, hc, hh, hadm, hl, hr, hzl, hzr⟩ := Y.chord_data hi
  zummy
  constructor
  · rintro (hreg | hreg)
    · exact Y.meet_of_regIn hh hAB hl hreg
    · exact Y.meet_of_regIn hh hAB hr hreg
  · zuibt
    obtain ⟨⟨qL, sL, hGL, hzGL⟩, ⟨qR, sR, hGR, hzGR⟩⟩ := Y.kept_ends hAB (hc ▸ hadm) hk
    obtain ⟨h6L, hpL, hlastL, hsideL⟩ := Y.end_ok hAB hl hGL (hzGL.trans hzl.symm)
    obtain ⟨h6R, hpR, hlastR, hsideR⟩ := Y.end_ok hAB hr hGR (hzGR.trans hzr.symm)
    have htzL := Y.tZ_iff hh hAB hl h6L hpL
    have htzR := Y.tZ_iff hh hAB hr h6R hpR
    -- a regular end gives the test
    have hreg : ∀ {p : ℕ} {t : ℝ}, 6 ≤ p → p ≤ 2 * C.m + 6 → ztkbx →
        (tZ (Qof P).n xH C.m C.topIdx C.sideBeta (NR.chord i).h p ↔ t = 0) →
        ¬ ztfcm →
        decide ztpi = li →
        RegIn (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h p := by
      intro p t h6 hp hlast htz hirr hside
      refine ⟨h6, hp, fun h' => htz.2 (hlast h'), fun ⟨hz, hk0⟩ => hirr ⟨htz.1 hz, ?_⟩, ?_⟩
      · rcases hk0 with h0 | h0
        · exact Or.inl ((tK_eq_zero_iff _ hm1 p).1 h0)
        · exact Or.inr ((tK_eq_m_iff _ hm1 p).1 h0)
      grind
    by_cases hirrL : (chainModel C).param zta (NR.chord i).lpos = 0 ∧
        (tU C.m C.topIdx C.sideBeta (NR.chord i).lp = 0 ∨
          tU C.m C.topIdx C.sideBeta (NR.chord i).lp = C.m)
    · by_cases hirrR : (chainModel C).param zta (NR.chord i).rpos = 0 ∧
          (tU C.m C.topIdx C.sideBeta (NR.chord i).rp = 0 ∨
            tU C.m C.topIdx C.sideBeta (NR.chord i).rp = C.m)
      · exfalso
        have hkL : tK C.m C.topIdx C.sideBeta (NR.chord i).lp = 0 ∨
            tK C.m C.topIdx C.sideBeta (NR.chord i).lp = C.m := by
          rcases hirrL.2 with h0 | h0
          · exact Or.inl ztlzt
          · exact Or.inr ztlzq
        have hkR : tK C.m C.topIdx C.sideBeta (NR.chord i).rp = 0 ∨
            tK C.m C.topIdx C.sideBeta (NR.chord i).rp = C.m := by
          rcases hirrR.2 with h0 | h0
          · exact Or.inl ztlzt
          · exact Or.inr ztlzq
        refine Y.not_both_irr hAB by_grind hk hkL hkR ?_ ?_
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
