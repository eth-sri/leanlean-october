module

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

/-- **The interior position of an end of a kept chord.** -/
theorem end_xpos {h : ℕ} {A B : ℝ} (hAB : A < B) {p : ℕ} {t : ℝ}
    (hat : SideAttach (C.sideWalk C.sideBeta) (hseg ((Qof P).vtx h).2 A B) p t) {q : ℕ} {s : ℝ}
    (hG : SideAttach xG (hseg ((Qof P).vtx h).2 A B) q s)
    (hpt : sidePt xG q s = sidePt (C.sideWalk C.sideBeta) p t) :
    (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge < (Qof P).n ∧
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧
      sidePt (interiorWalk (Qof P)) (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge τ =
        sidePt (C.sideWalk C.sideBeta) p t ∧
      ∃ a b : ℝ, (interiorModel (Qof P)).IsArc xS (reg r) a b ∧
        ((xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ = a ∨
          (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ = b ∨
          sideInArc a b ((xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge + τ)) := by
  have hm := Y.hm
  have h3 := Y.three
  have hm1 := C.one_le
  have hQ := Y.X.hQ
  have hFam := Y.X.hFam
  have hM : WalkAx (interiorModel (Qof P)) := walkAx_interiorModel hQ
  have hWn : (interiorWalk (Qof P)).n = (Qof P).n := walk_n _
  have hW : (interiorModel (Qof P)).W = interiorWalk (Qof P) := rfl
  obtain ⟨h6, hp, hlast, hside⟩ := Y.end_ok hAB hat hG hpt
  have hkc : tK C.m C.topIdx C.sideBeta p < xK := by
    have := tK_le C.sideBeta hm1 p (T := C.topIdx); omega
  have hι : sig li xK i0 (tK C.m C.topIdx C.sideBeta p) < xK := sig_lt li (by omega) _ _
  have hrep := Y.hrep _ hkc
  have hedge : (xPos (Qof P).n xH li C.m C.topIdx C.sideBeta h p).edge =
      ⌊hk (interiorModel (Qof P)) xS (reg r) (sig li xK i0 (tK C.m C.topIdx C.sideBeta p))⌋₊ :=
    pEdge_rep hQ hFam Y.X.hli Y.X.hdh hι hrep
  have hWv : C.P.vtx (tK C.m C.topIdx C.sideBeta p) =
      (xG).vtx (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) := Y.vtx_sig hkc
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  have hGn : (xG).n = xK := Y.gn
  rw [hedge]
  set ι := sig li xK i0 (tK C.m C.topIdx C.sideBeta p) with hιdef
  have hGv : (xG).vtx ι = hostPt (interiorModel (Qof P)).W (hk (interiorModel (Qof P)) xS (reg r) ι) :=
    hostPoly_vtx hι
  have hb := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hι)
  rw [hW, hWn] at hb
  set κ := hk (interiorModel (Qof P)) xS (reg r) ι with hκ
  have hq0 : ⌊κ⌋₊ < (Qof P).n := by
    have : (⌊κ⌋₊ : ℝ) < (Qof P).n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
    exact_mod_cast this
  have hf0 : 0 ≤ κ - ⌊κ⌋₊ := by have := Nat.floor_le hb.1; linarith
  have hf1 : κ - ⌊κ⌋₊ < 1 := by have := Nat.lt_floor_add_one κ; linarith
  refine ⟨hq0, ?_⟩
  have ht0 := hat.2.1
  have ht1 := hat.2.2.1
  rcases ht0.lt_or_eq with ht0' | ht0'
  · -- inside an arc piece
    have hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = li :=
      hside (by rintro ⟨h0, -⟩; exact ht0'.ne' h0)
    have hp' : p < 2 * C.m + 6 := by
      rcases lt_or_eq_of_le hp with h' | h'
      · exact h'
      · exact absurd (hlast h') ht0'.ne'
    obtain ⟨hz, hsec⟩ := Y.inner_edge h6 hp' ⟨ht0', ht1⟩ hA
    rw [← hιdef] at hz hsec
    have hGat : SideAttach xG (hseg ((Qof P).vtx h).2 A B) ι t :=
      ExtG.attach_of_sector hz.symm (fun x hx => (hsec x).1 hx) (by rw [hGn]; exact hι) ht0 ht1 hat
    -- the gap after `ι` is an arc gap
    have hAg : ArcGap (interiorModel (Qof P)) xS (reg r) ι := by
      rcases gap_cases hM hFam.2.1 hFam.1 Y.X.hne Y.X.hR (by omega) hι with hAg | hCg
      · exact hAg
      · exact (Y.not_attach_flat hAB hι ⟨ht0', ht1⟩ (Y.chordGap_flat hι hCg) hGat).elim
    have hι1 : (ι + 1) % xK < xK := Nat.mod_lt _ (by omega)
    have hb' := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hι1)
    rw [hW, hWn] at hb'
    set κ' := hk (interiorModel (Qof P)) xS (reg r) ((ι + 1) % xK) with hκ'
    have hne : κ ≠ κ' := hk_succ_ne hM hFam.2.1 hFam.1 (by omega) hι
    have hnoint : ∀ k : ℕ, k < (Qof P).n → ¬ sideInArc κ κ' k := fun k hk' =>
      arcGap_noInt hQ hFam Y.X.hne Y.X.hR hι hAg k (by rw [hW, hWn]; exact hk')
    -- the next host point is on the same walk edge, at a larger parameter
    obtain ⟨f', hff', hf'1, hnext, hin⟩ : ∃ f' : ℝ, κ - ⌊κ⌋₊ < f' ∧ f' ≤ 1 ∧
        hostPt (interiorWalk (Qof P)) κ' = sidePt (interiorWalk (Qof P)) ⌊κ⌋₊ f' ∧
        ∀ x : ℝ, κ < ⌊κ⌋₊ + x → x < f' →
          0 ≤ (⌊κ⌋₊ : ℝ) + x ∧ (⌊κ⌋₊ : ℝ) + x < (Qof P).n ∧ sideInArc κ κ' (⌊κ⌋₊ + x) := by
      rcases noInt_cases hb.1 hb.2 hb'.1 hb'.2 hne hnoint with ⟨hlt, hfl⟩ | hyv
      · refine ⟨κ' - ⌊κ⌋₊, by linarith, ?_, ?_, fun x hx1 hx2 => ⟨by linarith [hb.1], by linarith [hb'.2], ?_⟩⟩
        · have := Nat.lt_floor_add_one κ'; rw [hfl] at this; linarith
        · unfold hostPt; rw [hfl]
        · unfold sideInArc; rw [ite_eq_left hlt]; constructor <;> linarith
      · have hq1 : ((⌊κ⌋₊ : ℝ) + 1) ≤ (Qof P).n := by exact_mod_cast hq0
        refine ⟨1, by linarith, le_rfl, ?_, fun x hx1 hx2 => ⟨by linarith [hb.1], by linarith, ?_⟩⟩
        · rw [hyv]; unfold hostPt
          rw [Nat.floor_natCast, sub_self, Chazelle.Chain.sidePt_zero, sidePt_one, hWn]
        · by_cases hq1' : ⌊κ⌋₊ + 1 < (Qof P).n
          · rw [hyv, Nat.mod_eq_of_lt hq1']
            have hκ1 : κ < (⌊κ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one κ
            unfold sideInArc; rw [ite_eq_left (by push_cast; linarith)]
            push_cast; constructor <;> linarith
          · rw [hyv, show ⌊κ⌋₊ + 1 = (Qof P).n by omega, Nat.mod_self]
            unfold sideInArc; rw [ite_eq_right (by push_cast; linarith [hb.1])]
            left; linarith
    -- the end
    have hτ0 : 0 < t * (f' - (κ - ⌊κ⌋₊)) := mul_pos ht0' (by linarith)
    have hτ1 : t * (f' - (κ - ⌊κ⌋₊)) < f' - (κ - ⌊κ⌋₊) := by nlinarith
    refine ⟨(κ - ⌊κ⌋₊) + t * (f' - (κ - ⌊κ⌋₊)), by linarith, by linarith, ?_, ?_⟩
    · rw [hz]
      have e1 : (xG).vtx ι = sidePt (interiorWalk (Qof P)) ⌊κ⌋₊ (κ - ⌊κ⌋₊) := by rw [hGv]; rfl
      have e2 : (xG).vtx ((ι + 1) % (xG).n) = sidePt (interiorWalk (Qof P)) ⌊κ⌋₊ f' := by
        rw [hGn, hostPoly_vtx hι1]; exact hnext
      symm
      show lerp ((xG).vtx ι) ((xG).vtx ((ι + 1) % (xG).n)) t = _
      rw [e1, e2]
      unfold sidePt
      rw [DownHost.lerp_lerp]
    · obtain ⟨a, b, harc, hsub⟩ := hAg
      have hx := hin ((κ - ⌊κ⌋₊) + t * (f' - (κ - ⌊κ⌋₊))) (by linarith) (by linarith)
      exact ⟨a, b, harc, Or.inr (Or.inr (hsub _ hx.1 (by rw [hW, hWn]; exact hx.2.1) hx.2.2))⟩
  · -- at a host point
    subst ht0'
    have hz0 : sidePt (C.sideWalk C.sideBeta) p 0 = (xG).vtx ι := by
      rw [Chazelle.Chain.sidePt_zero, hv0, hWv]
    refine ⟨κ - ⌊κ⌋₊, hf0, hf1, ?_, ?_⟩
    · rw [hz0, hGv]; rfl
    · rw [show (⌊κ⌋₊ : ℝ) + (κ - ⌊κ⌋₊) = κ by ring]
      rcases hk_mem hM hFam.2.1 hFam.1 hι with hex | hvx
      · have hcut := exitKeys_subset_cuts hex
        rcases gap_cases hM hFam.2.1 hFam.1 Y.X.hne Y.X.hR (by omega) hι with hAg | hCg
        · obtain ⟨b, harc⟩ := start_of_arcGap hQ hFam Y.X.hne Y.X.hR hι hAg hcut
          exact ⟨κ, b, harc, Or.inl rfl⟩
        · have hpv : prevIdx xK ι < xK := prevIdx_lt (by omega)
          have hsp : (prevIdx xK ι + 1) % xK = ι := succ_prevIdx hι
          rcases gap_cases hM hFam.2.1 hFam.1 Y.X.hne Y.X.hR (by omega) hpv with hAg' | hCg'
          · obtain ⟨a', b', harc, hsub⟩ := hAg'
            rw [hsp] at hsub
            have hbp := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hpv)
            rw [hW, hWn] at hbp
            have hne' : hk (interiorModel (Qof P)) xS (reg r) (prevIdx xK ι) ≠ κ := by
              have := hk_succ_ne hM hFam.2.1 hFam.1 (by omega) hpv; rwa [hsp] at this
            have hbn : b' < (Qof P).n := by have := harc.2.2.2.1; rwa [hW, hWn] at this
            have e := cyc_end hne' hbp.1 hbp.2 hb.1 hb.2 harc.2.2.1 hbn
              (fun z hz0 hzn hz => hsub z hz0 (by rw [hW, hWn]; exact hzn) hz)
              (fun hin => harc.2.2.2.2.2.1 _ hin hcut)
            exact ⟨a', b', harc, Or.inr (Or.inl e)⟩
          · exfalso
            have hGpos : sidePt xG q s = sidePt xG ι 0 := by
              rw [hpt, hz0, Chazelle.Chain.sidePt_zero]
            obtain ⟨hqι, hs0⟩ := FactsInterior.pos_unique Y.gSimple
              hG.1 (by rw [hGn]; exact hι) hG.2.1 hG.2.2.1 le_rfl one_pos hGpos
            have h1 := Y.chordGap_flat hι hCg
            have h2 := Y.chordGap_flat hpv hCg'
            rw [hsp] at h2
            rw [hqι, hs0] at hG
            exact Y.not_attach_junction hAB hι h1 h2 hG
      · obtain ⟨k, -, hkk, a, b, harc, hin⟩ := hvx
        have hkk' : κ = k := hkk
        exact ⟨a, b, harc, Or.inr (Or.inr (by rw [hkk']; exact hin))⟩

/-- An arc of the region gives an arc record of region `r` of `N`. -/
theorem onArc_of {x : WPos} {a b : ℝ}
    (harc : (interiorModel (Qof P)).IsArc xS (reg r) a b)
    (hx : (interiorModel (Qof P)).key (Qof P) x = a ∨ (interiorModel (Qof P)).key (Qof P) x = b ∨
      sideInArc a b ((interiorModel (Qof P)).key (Qof P) x)) :
    ∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
      OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j x := by
  obtain ⟨-, -, hcomp⟩ := regArcs_facts Y.X.hQ Y.X.hL Y.X.hperm Y.X.hsort Y.X.hK Y.X.hregs Y.X.hr
  obtain ⟨t, ht, hs, he⟩ := hcomp a b harc
  refine ⟨((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs.getD t 0, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  · unfold OnArcKey; rw [hs, he]; exact hx

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
  have hn3 : 3 ≤ (Qof P).n := Chazelle.Jordan.simple_three_le hQ
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
  have hparL : (interiorModel (Qof P)).param (Qof P) xL = τL :=
    iparam Y.X.hli Y.X.hdh (by omega) heL (by rw [hpL])
  have hparR : (interiorModel (Qof P)).param (Qof P) xR = τR :=
    iparam Y.X.hli Y.X.hdh (by omega) heR (by rw [hpR])
  have hposL : (interiorModel (Qof P)).pos (Qof P) xL = ((A, y) : Point) := by
    show sidePt (interiorWalk (Qof P)) xL.edge ((interiorModel (Qof P)).param (Qof P) xL) = _
    rw [hparL, hpL]
  have hposR : (interiorModel (Qof P)).pos (Qof P) xR = ((B, y) : Point) := by
    show sidePt (interiorWalk (Qof P)) xR.edge ((interiorModel (Qof P)).param (Qof P) xR) = _
    rw [hparR, hpR]
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
  obtain ⟨hIadm, -⟩ := Y.hext.loc (F₁ := {hseg y A B}) (by simpa using hadm) _ ⟨rfl, hk⟩
  have hMQ : WalkAx (interiorModel (Qof P)) := walkAx_interiorModel hQ
  obtain ⟨a', b', -, hseg', hy', -, hEa, hEb⟩ := hMQ.ends _ hIadm
  have hWs := (FactsInterior.interiorWalk_spec hQ).1
  have hWn : (interiorWalk (Qof P)).n = (Qof P).n := walk_n _
  have hattach : ∀ (z : Point) (e : ℕ) (τ : ℝ), e < (Qof P).n → 0 ≤ τ → τ < 1 →
      sidePt (interiorWalk (Qof P)) e τ = z → (z = a' ∨ z = b') →
      SideAttach (interiorWalk (Qof P)) (hseg y A B) e τ := by
    intro z e τ he hτ0 hτ1 hpt hz
    obtain ⟨q₁, s₁, hA₁, hp₁⟩ : ∃ q₁ s₁, SideAttach (interiorWalk (Qof P)) (hseg y A B) q₁ s₁ ∧
        sidePt (interiorWalk (Qof P)) q₁ s₁ = z := by
      rcases hz with rfl | rfl
      · exact hEa.1
      · exact hEb.1
    obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hWs (by rw [hWn]; exact he) hA₁.1 hτ0 hτ1
      hA₁.2.1 hA₁.2.2.1 (hpt.trans hp₁.symm)
    exact hA₁
  refine ⟨hset, ?_, hh, ⟨by rw [hparL]; exact hτL0, by rw [hparL]; exact hτL1, by
      show (NR.chord i).h + 1 ≤ (Qof P).n; omega⟩,
    ⟨by rw [hparR]; exact hτR0, by rw [hparR]; exact hτR1, by
      show (NR.chord i).h + 1 ≤ (Qof P).n; omega⟩, ?_, ?_⟩
  · unfold CRec.Attached
    rw [hset, hlpos, hrpos, hparL, hparR]
    exact ⟨hattach _ _ _ heL hτL0 hτL1 hpL (DownDrv.left_end_of_segment hAB hy' hseg'),
      hattach _ _ _ heR hτR0 hτR1 hpR (right_end_of_segment hAB hy' hseg')⟩
  · have hkey : (interiorModel (Qof P)).key (Qof P) xL = xL.edge + τL := by
      show xL.edge + (interiorModel (Qof P)).param (Qof P) xL = _; rw [hparL]
    refine Y.onArc_of harcL ?_
    rw [hkey]; exact hxL
  · have hkey : (interiorModel (Qof P)).key (Qof P) xR = xR.edge + τR := by
      show xR.edge + (interiorModel (Qof P)).param (Qof P) xR = _; rw [hparR]
    refine Y.onArc_of harcR ?_
    rw [hkey]; exact hxR

end XCtx

end

end

end DrvX

end Chazelle.Core
