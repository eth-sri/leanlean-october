module
public import Chazelle.MacT

public import Chazelle.Core.DownPhaseDrvXPos

/-!
# Down phase, extraction (D6): X-R2, the interior triple of a kept chord

* `end_xpos`: an end of a kept chord is the point of the interior walk position
  `⟨(xPos …).edge, τ⟩`, `τ ∈ [0, 1)`, and its key lies on the closure of an arc of the region;
* `kept_pos`: the interior triple `xTriple …` of a kept chord record describes the same chord,
  attached in the interior model, with proper end positions on arcs of the region `r` of `N`.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set DownHost DownMath
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw sideInArc IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)
open BuildNF (buildNF)
open DrvR (regHost ivB qE OnArcKey)

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

/-- **The interior position of an end of a kept chord.** -/
theorem end_xpos {h : ℕ} {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach ztcs ztwu p t) {q : ℕ} {s : ℝ}
    (hG : SideAttach xG ztwu q s)
    (hpt : sidePt xG q s = sidePt ztcs p t) :
    (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge < (Qof P).n ∧
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧
      sidePt ztwsc (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge τ =
        sidePt ztcs p t ∧
      ∃ a b : ℝ, (interiorModel zta).IsArc xS ztcz a b ∧
        ((xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ = a ∨
          (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ = b ∨
          sideInArc a b ((xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ)) := by
  zukj

  zubb
  have hQ := Y.X.hQ
  have hFam := Y.X.hFam
  zubwf
  have hWn : ztkzf := walk_n _
  have hW : (interiorModel _).W = interiorWalk zta := rfl
  obtain ⟨h6, hp, hlast, hside⟩ := Y.end_ok hAB hat hG hpt
  have hkc : tK C.m C.topIdx C.sideBeta p < xK := by
    have := tK_le C.sideBeta hm1 p (T := C.topIdx); omega
  have hι : sig li xK i0 ztqn < xK := sig_lt li by_omega _ _
  have hrep := Y.hrep _ hkc
  have hedge : (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge =
      ⌊hk (interiorModel (Qof P)) xS (reg r) (sig li xK i0 (tK C.m C.topIdx C.sideBeta p))⌋₊ :=
    pEdge_rep hQ hFam Y.X.hli Y.X.hdh hι hrep
  have hWv := Y.vtx_sig hkc
  zuhfr
  zumbt
  zuowj
  set ι := sig li xK i0 ztqn with hιdef
  have hGv :=
    hostPoly_vtx hι
  zuljr
  rw [hW, hWn] at hb
  set κ := hk ztwiq xS ztcz ι with hκ
  have hq0 : ⌊κ⌋₊ < (Qof P).n := by
    zuepf
    zufc
  zucap

  refine ⟨hq0, ?_⟩
  zuiam

  zucox
  · -- inside an arc piece
    have hA : decide _ = li :=
      hside by_grind
    have hp' : ztjaa := by
      grind
    obtain ⟨hz, hsec⟩ := Y.inner_edge h6 hp' ztkls hA
    rw [← hιdef] at hz hsec
    have hGat :=
      ExtG.attach_of_sector hz.symm (fun x hx => (hsec x).1 hx) by_omega ht0 ht1 hat
    -- the gap after `ι` is an arc gap
    have hAg : ArcGap ztwiq xS ztcz ι := by
      zuevi
      · omega
      · exact (Y.not_attach_flat hAB hι by_grind (Y.chordGap_flat hι hCg) hGat).elim
    have hι1 : ztfvp % xK < xK := Nat.mod_lt _ by_omega
    have hb' := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hι1)
    rw [hW, hWn] at hb'
    set κ' := hk (interiorModel (Qof P)) xS (reg r) ((ι + 1) % xK) with hκ'
    have hne : κ ≠ κ' := hk_succ_ne hM hFam.2.1 hFam.1 (by omega) hι
    have hnoint : ∀ k : ℕ, k < (Qof P).n → ¬ sideInArc κ κ' k := fun k hk' =>
      arcGap_noInt hQ hFam Y.X.hne Y.X.hR hι hAg k (by grind)
    -- the next host point is on the same walk edge, at a larger parameter
    obtain ⟨f', hff', hf'1, hnext, hin⟩ : ∃ f' : ℝ, κ - ⌊κ⌋₊ < f' ∧ f' ≤ 1 ∧
        hostPt ztwsc κ' = sidePt ztwsc ⌊κ⌋₊ f' ∧
        ∀ x : ℝ, κ < ⌊κ⌋₊ + x → x < f' →
          0 ≤ (⌊κ⌋₊ : ℝ) + x ∧ (⌊κ⌋₊ : ℝ) + x < (Qof P).n ∧ sideInArc κ κ' (⌊κ⌋₊ + x) := by
      rcases noInt_cases hb.1 hb.2 hb'.1 hb'.2 hne hnoint with ⟨hlt, hfl⟩ | hyv
      · refine ⟨κ' - ⌊κ⌋₊, by linarith, ?_, ?_, fun x hx1 hx2 => ⟨by grind, by grind, ?_⟩⟩
        · have := Nat.lt_floor_add_one κ'; grind
        · unfold hostPt; rw [hfl]
        · zujv
      · have hq1 : ((⌊κ⌋₊ : ℝ) + 1) ≤ (Qof P).n := by exact_mod_cast hq0
        refine ⟨1, by_linarith, le_rfl, ?_, fun x hx1 hx2 => ⟨by_grind, by_linarith, ?_⟩⟩
        · rw [hyv]; unfold hostPt
          rw [Nat.floor_natCast, sub_self, Chazelle.Chain.sidePt_zero, sidePt_one, hWn]
        · by_cases hq1' : ⌊κ⌋₊ + 1 < (Qof P).n
          · rw [hyv, Nat.mod_eq_of_lt hq1']
            have hκ1 := Nat.lt_floor_add_one κ
            zujv
          · rw [hyv, show ⌊κ⌋₊ + 1 = (Qof P).n by omega, Nat.mod_self]
            zujv
    -- the end
    have hτ0 : 0 < t * ztxwo := mul_pos ht0' by_linarith
    have hτ1 : t * ztxwo < f' - ztbkw := by_nlinarith
    refine ⟨ztbkw + t * ztxwo, by_linarith, by_linarith, ?_, ?_⟩
    · zudur
      have e1 : (xG).vtx ι = sidePt ztwsc ⌊κ⌋₊ ztbkw := by_tauto
      have e2 : (xG).vtx ((ι + 1) % (xG).n) = sidePt (interiorWalk (Qof P)) ⌊κ⌋₊ f' := by
        rw [hGn, hostPoly_vtx hι1]; grind
      symm
      show lerp ((xG).vtx ι) ((xG).vtx ((ι + 1) % (xG).n)) t = _
      zuea
      zucky
      rw [DownHost.lerp_lerp]
    · obtain ⟨a, b, harc, hsub⟩ := hAg
      have hx := hin (ztbkw + t * ztxwo) by_linarith by_linarith
      exact ⟨a, b, harc, Or.inr (Or.inr (hsub _ hx.1 by_grind hx.2.2))⟩
  · -- at a host point
    zultg
    have hz0 : sidePt ztcs p 0 = (xG).vtx ι := by
      rw [Chazelle.Chain.sidePt_zero, hv0, hWv]
    refine ⟨κ - ⌊κ⌋₊, hf0, hf1, ?_, ?_⟩
    · rw [hz0, hGv]; rfl
    · rw [show (⌊κ⌋₊ : ℝ) + ztbkw = κ by ring]
      rcases hk_mem hM hFam.2.1 hFam.1 hι with hex | hvx
      · have hcut := exitKeys_subset_cuts hex
        zuevi
        · obtain ⟨b, harc⟩ := start_of_arcGap hQ hFam Y.X.hne Y.X.hR hι hAg hcut
          grind
        · have hpv : prevIdx xK ι < xK := prevIdx_lt by_omega
          have hsp := succ_prevIdx hι
          rcases gap_cases hM hFam.2.1 hFam.1 Y.X.hne Y.X.hR by_omega hpv with hAg' | hCg'
          · obtain ⟨a', b', harc, hsub⟩ := hAg'
            rw [hsp] at hsub
            have hbp := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hpv)
            rw [hW, hWn] at hbp
            have hne' : hk (interiorModel (Qof P)) xS (reg r) (prevIdx xK ι) ≠ κ := by
              have := hk_succ_ne hM hFam.2.1 hFam.1 by_omega hpv; grind
            have hbn : b' < (Qof P).n := by have := harc.2.2.2.1; grind
            have e := cyc_end hne' hbp.1 hbp.2 hb.1 hb.2 harc.2.2.1 hbn
              by_grind
              (fun hin => harc.2.2.2.2.2.1 _ hin hcut)
            exact ⟨a', b', harc, by_grind⟩
          · exfalso
            have hGpos : sidePt xG q s = sidePt xG ι 0 := by
              rw [hpt, hz0, Chazelle.Chain.sidePt_zero]
            obtain ⟨hqι, hs0⟩ := FactsInterior.pos_unique Y.gSimple
              hG.1 by_omega hG.2.1 hG.2.2.1 le_rfl one_pos hGpos
            have h1 := Y.chordGap_flat hι hCg
            have h2 := Y.chordGap_flat hpv hCg'
            rw [hsp] at h2
            rw [hqι, hs0] at hG
            exact Y.not_attach_junction hAB hι h1 h2 hG
      · obtain ⟨k, -, hkk, a, b, harc, hin⟩ := hvx
        grind

/-- An arc of the region gives an arc record of region `r` of `N`. -/
theorem onArc_of {x : WPos} {a b : ℝ}
    (harc : (interiorModel zta).IsArc xS ztcz a b)
    (hx : (interiorModel zta).key zta x = a ∨ (interiorModel zta).key zta x = b ∨
      sideInArc a b ((interiorModel zta).key zta x)) :
    ∃ j ∈ ((buildNF ztwiq zta L E).region r).arcs,
      OnArcKey zta ztbajc j x := by
  obtain ⟨-, -, hcomp⟩ := regArcs_facts Y.X.hQ Y.X.hL Y.X.hperm Y.X.hsort Y.X.hK Y.X.hregs Y.X.hr
  obtain ⟨t, ht, hs, he⟩ := hcomp a b harc
  refine ⟨((buildNF ztwiq zta L E).region r).arcs.getD t 0, ?_, ?_⟩
  · simp_all
  · unfold OnArcKey; simp_all

/-- **X-R2: the interior triple of a kept chord record.** -/
theorem kept_pos {i : ℕ} (hi : i < NR.nChords)
    (hk : ((NR.chord i).toSet (chainModel C) (Qof P) ∩ reg r).Nonempty) :
    (recOf (xTriple (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp
        (NR.chord i).rp)).toSet (interiorModel (Qof P)) (Qof P) =
      (NR.chord i).toSet (chainModel C) (Qof P) ∧
    (recOf (xTriple (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp
        (NR.chord i).rp)).Attached (interiorModel (Qof P)) (Qof P) ∧
    (NR.chord i).h < (Qof P).n ∧
    ProperPos (interiorModel (Qof P)) (Qof P) (Qof P).n
      (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp) ∧
    ProperPos (interiorModel (Qof P)) (Qof P) (Qof P).n
      (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).rp) ∧
    (∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
      OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j
        (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp)) ∧
    (∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
      OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j
        (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).rp)) := by
  have hQ := Y.X.hQ
  have hn3 := Chazelle.Jordan.simple_three_le hQ
  obtain ⟨A, B, hAB, hc, hh, hadm, hl, hr, hzl, hzr⟩ := Y.chord_data hi
  rw [hc] at hk hadm ⊢
  obtain ⟨⟨qL, sL, hGL, hzGL⟩, ⟨qR, sR, hGR, hzGR⟩⟩ := Y.kept_ends hAB hadm hk
  obtain ⟨heL, τL, hτL0, hτL1, hpL, aL, bL, harcL, hxL⟩ :=
    Y.end_xpos hAB hl hGL (hzGL.trans hzl.symm)
  obtain ⟨heR, τR, hτR0, hτR1, hpR, aR, bR, harcR, hxR⟩ :=
    Y.end_xpos hAB hr hGR (hzGR.trans hzr.symm)
  rw [hzl] at hpL
  rw [hzr] at hpR
  set y := ((Qof P).vtx (NR.chord i).h).2 with hydef
  set xL := xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).lp with hxLdef
  set xR := xPos (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h (NR.chord i).rp with hxRdef
  -- parameters and points
  have hparL : (interiorModel _).param _ xL = τL :=
    iparam Y.X.hli Y.X.hdh (by omega) heL (by rw [hpL])
  have hparR : (interiorModel _).param _ xR = τR :=
    iparam Y.X.hli Y.X.hdh (by omega) heR (by rw [hpR])
  have hposL : (interiorModel (Qof P)).pos (Qof P) xL = ((A, y) : Point) := by
    show sidePt (interiorWalk _) xL.edge _ = _
    simp_all
  have hposR : (interiorModel (Qof P)).pos (Qof P) xR = ((B, y) : Point) := by
    show sidePt (interiorWalk _) xR.edge _ = _
    simp_all
  have hlpos : (recOf (xTriple (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h
      (NR.chord i).lp (NR.chord i).rp)).lpos = xL := rfl
  have hrpos : (recOf (xTriple (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h
      (NR.chord i).lp (NR.chord i).rp)).rpos = xR := rfl
  have hset : (recOf (xTriple (Qof P).n xH li C.m C.topIdx C.sideBeta (NR.chord i).h
      (NR.chord i).lp (NR.chord i).rp)).toSet (interiorModel (Qof P)) (Qof P) = hseg y A B := by
    unfold CRec.toSet
    rw [hlpos, hrpos, hposL, hposR]
    rfl
  -- the chord is an interior chord of `Q`, attached at its ends
  obtain ⟨hIadm, -⟩ := Y.hext.loc (F₁ := {hseg y A B}) (by simp_all) _ ⟨rfl, hk⟩
  have hMQ : WalkAx _ := walkAx_interiorModel hQ
  obtain ⟨a', b', -, hseg', hy', -, hEa, hEb⟩ := hMQ.ends _ hIadm
  have hWs := (FactsInterior.interiorWalk_spec hQ).1
  have hWn : (interiorWalk _).n = (Qof P).n := walk_n _
  have hattach : ∀ (z : Point) (e : ℕ) (τ : ℝ), e < (Qof P).n → 0 ≤ τ → τ < 1 →
      sidePt (interiorWalk (Qof P)) e τ = z → (z = a' ∨ z = b') →
      SideAttach (interiorWalk (Qof P)) (hseg y A B) e τ := by
    intro z e τ he hτ0 hτ1 hpt hz
    obtain ⟨q₁, s₁, hA₁, hp₁⟩ : ∃ q₁ s₁, SideAttach (interiorWalk (Qof P)) (hseg y A B) q₁ s₁ ∧
        sidePt (interiorWalk (Qof P)) q₁ s₁ = z := by
      rcases hz with rfl | rfl
      · exact hEa.1
      · exact hEb.1
    obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hWs (by omega) hA₁.1 hτ0 hτ1
      hA₁.2.1 hA₁.2.2.1 (hpt.trans hp₁.symm)
    omega
  refine ⟨hset, ?_, hh, ⟨by grind, by grind, by
      tauto⟩,
    ⟨by grind, by grind, by
      tauto⟩, ?_, ?_⟩
  · unfold CRec.Attached
    rw [hset, hlpos, hrpos, hparL, hparR]
    exact ⟨hattach _ _ _ heL hτL0 hτL1 hpL (DownDrv.left_end_of_segment hAB hy' hseg'),
      hattach _ _ _ heR hτR0 hτR1 hpR (right_end_of_segment hAB hy' hseg')⟩
  · have hkey : (interiorModel (Qof P)).key (Qof P) xL = xL.edge + τL := by
      show xL.edge + (interiorModel _).param _ xL = _; grind
    refine Y.onArc_of harcL ?_
    grind
  · have hkey : (interiorModel (Qof P)).key (Qof P) xR = xR.edge + τR := by
      show xR.edge + (interiorModel _).param _ xR = _; grind
    refine Y.onArc_of harcR ?_
    grind

end XCtx

end

end

end DrvX

end Chazelle.Core
