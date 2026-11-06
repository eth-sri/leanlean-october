module

public import Chazelle.Core.SweepEvStopFin7A
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 2: the emission of the raw records

**`slfEmits_spec : SlfEmitsSpec`**: the raw records of the attachments `A₀` (code `dc = b`) and
`A₁` (code `dc = 1 - b`) on the `C₁` part are emitted and valid (`orig_attach`), and every
attachment of the stop chord on the `C₁` part is one of them (`attach_two`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

theorem slfEmits_spec : SlfEmitsSpec := by
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD arr0 pw0 arr1 pw1 bit0 bit1 hax hR0 hR1 hroom
  set kind := c.nreg oKd with hkind
  set k := c.nreg oKk with hkk
  set b := c.nreg oB with hbb
  set e := stopSet J (Qof P) N₂ kind k b with he
  have hb  := hD.ok.2.1
  obtain ⟨i1, i2, -⟩ := orig_attach E.hP E.hNF₂ hD
  obtain ⟨A0, pt0⟩ := i1 _ _ arr0
  obtain ⟨A1, pt1⟩ := i2 _ _ arr1
  have hK := E.hK.fix hI
  have hX : ∀ r, r = oF0 + 1 ∨ r = oF0 + 2 ∨ r = oB ∨ r = a1F + 1 ∨ r = a1F + 2 ∨ r = slfDc →
      r ≠ slfX := by
    intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [oF0, oB, a1F, slfDc, slfX, sw] <;> omega
  -- 1. the reversed code
  refine (IRS.seq (K₁ := 1) (K₂ := 37 + 37) (IRS.block [.subN slfDc K1 oB] hI
    ⟨iscr_sw (by ufo slfDc sw) (by ufo slfDc sw), trivial⟩) ?_).mono
    (by norm_num) (fun _ => id)
  rintro c₁ hI₁ - - rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.subN slfDc K1 oB] c.nreg } with hc₁
  have v1 : c₁.nreg slfDc = 1 - b := by simp [hc₁, regB, regI, upd, hK.2.1, hbb]
  have k1 : ∀ q, q ≠ slfDc → c₁.nreg q = c.nreg q := fun q hq => by
    simp [hc₁, regB, regI, upd, hq]
  have rr1 : ∀ q, (sw 4000 ≤ q ∧ q ≤ sw 4066) ∨ q = K0 ∨ q = K1 ∨ q = ALLOC →
      c₁.nreg q = c.nreg q := fun q hq => k1 q (by
        rcases hq with h | rfl | rfl | rfl <;> simp [slfDc, K0, K1, ALLOC, sw] at * <;> omega)
  have c1RB : c₁.nreg gRB = c.nreg gRB := rr1 _ (Or.inl ⟨by ufo gRB, by ufo gRB sw⟩)
  have c1RC : c₁.nreg gRC = c.nreg gRC := rr1 _ (Or.inl ⟨by ufo gRC sw, by ufo gRC sw⟩)
  have c1O : c₁.nreg slfO = c.nreg slfO := rr1 _ (Or.inl ⟨by ufo slfO sw, by ufo slfO sw⟩)
  -- 2. the record of `A₀`
  refine IRS.seq (K₁ := 37) (K₂ := 37) (slfMaybe_irs (bitr := slfO) (hX _ (Or.inl rfl))
    (hX _ (Or.inr (Or.inl rfl))) (hX _ (Or.inr (Or.inr (Or.inl rfl)))) hI₁
    (by rw [rr1 _ (Or.inr (Or.inl rfl))]; exact hK.1) (by rw [rr1 _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hK.2.1)
    (by rwx [c1RB]) (by rw [c1RB, c1RC]; have := hI.hw.1 ALLOC; omega)
    (by rw [c1O]; exact bit0.1)) ?_
  rintro c₂ hI₂ - - ⟨g2, w2, m2, r2⟩
  simp [c1O, c1RC, c1RB] at g2 w2 m2
  have c2r : ∀ q, q ≠ slfX → q ≠ gRC → q ≠ slfDc → c₂.nreg q = c.nreg q :=
    fun q h1 h2 h3 => (r2 q h1 h2).trans (k1 q h3)
  have c2RB : c₂.nreg gRB = c.nreg gRB :=
    c2r _ (by ufo gRB slfX sw) (by ufo gRB gRC sw) (by ufo gRB slfDc sw)
  have c2O4 : c₂.nreg (slfO + 4) = c.nreg (slfO + 4) :=
    c2r _ (by ufo slfO slfX sw) (by ufo slfO gRC sw) (by ufo slfO slfDc sw)
  have c2Dc : c₂.nreg slfDc = 1 - b := by
    rw [r2 _ (by ufo slfDc slfX sw) (by ufo slfDc gRC sw), v1]
  have hgrc2 : c₂.nreg gRC ≤ c.nreg gRC + 1 := by rw [g2]; splao
  -- 3. the record of `A₁`
  refine (slfMaybe_irs (bitr := slfO + 4) (hX _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (hX _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (hX _ (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr rfl)))))) hI₂
    (by rw [c2r _ (by ufo K0 slfX sw) (by ufo K0 gRC sw)
      (by ufo K0 slfDc sw)]; exact hK.1)
    (by rw [c2r _ (by ufo K1 slfX sw) (by ufo K1 gRC sw)
      (by ufo K1 slfDc sw)]; exact hK.2.1)
    (by rwx [c2RB]) (by rw [c2RB]; have := hI.hw.1 ALLOC; omega)
    (by rw [c2O4]; exact bit1.1)).mono (by norm_num) ?_
  rintro c' ⟨g3, w3, m3, r3⟩
  simp [c2O4, c2RB] at g3 w3 m3
  -- the facts
  set t₀ := (chainModel J.whole).param (Qof P) ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩ with ht₀
  set t₁ := (chainModel J.whole).param (Qof P) ⟨c.nreg (a1F + 1), c.nreg (a1F + 2)⟩ with ht₁
  have hE0 : c.nreg slfO ≠ 1 → (Lst J : ℝ) ≤ oW J (c.nreg (oF0 + 1) + t₀) := fun h => by
    have := bit0.2; unfold slfOff at this; by_contra hc; push Not at hc
    exact h (this.2 hc)
  have hE1 : c.nreg (slfO + 4) ≠ 1 → (Lst J : ℝ) ≤ oW J (c.nreg (a1F + 1) + t₁) := fun h => by
    have := bit1.2; unfold slfOff at this; by_contra hc; push Not at hc
    exact h (this.2 hc)
  have hN0 : c.nreg slfO = 1 → oW J (c.nreg (oF0 + 1) + t₀) < Lst J := fun h => by
    have := bit0.2; unfold slfOff at this; exact this.1 h
  have hN1 : c.nreg (slfO + 4) = 1 → oW J (c.nreg (a1F + 1) + t₁) < Lst J := fun h => by
    have := bit1.2; unfold slfOff at this; exact this.1 h
  -- the record of `A₀` in `c'`
  have rec0 : c.nreg slfO ≠ 1 → RawV P J N₂ c'.nmem (c.nreg gRB) (c.nreg gRC) ∧
      rawRec c'.nmem (c.nreg gRB) (c.nreg gRC) =
        (c.nreg (oF0 + 1), c.nreg (oF0 + 2), kind, k, b) := by
    intro h
    obtain ⟨q1, q2, q3⟩ := slfRec_words (cc := c₁) (w2 h)
    have hc' := slfRec_congr (m := c₂.nmem) (m' := c'.nmem) (RB := c.nreg gRB) (j := c.nreg gRC)
      (fun i hi => m3 _ (Or.inl (by rwo [g2, ite_eq_right h])))
    rw [← hc'.1] at q1
    rw [← hc'.2.1] at q2
    rw [← hc'.2.2] at q3
    have g : ∀ q, (q = oF0 + 1 ∨ q = oF0 + 2 ∨ q = oKd ∨ q = oKk ∨ q = oB ∨ q = slfA ∨ q = slfN ∨
        q = slfL0 ∨ q = slfL1 ∨ q = oPar) → c₁.nreg q = c.nreg q := by
      intro q hq
      exact k1 q (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [oF0, oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfDc, sw] <;> omega)
    rw [g (oF0 + 1) (by simp), g (oF0 + 2) (by simp), g oKd (by simp), g oKk (by simp),
      g oB (by simp)] at q1
    rw [g oB (by simp)] at q2
    rw [g slfA (by simp), g slfN (by simp), g slfL0 (by simp), g slfL1 (by simp),
      g oPar (by simp)] at q3
    refine ⟨slfRawV hD hb A0 pt0 (hE0 h) pw0 (hax ⟨_, _, A0, hE0 h⟩) q1 q2 q3, q1⟩
  -- the record of `A₁` in `c'`
  have rec1 : c.nreg (slfO + 4) ≠ 1 → RawV P J N₂ c'.nmem (c.nreg gRB) (c₂.nreg gRC) ∧
      rawRec c'.nmem (c.nreg gRB) (c₂.nreg gRC) =
        (c.nreg (a1F + 1), c.nreg (a1F + 2), kind, k, b) := by
    intro h
    obtain ⟨q1, q2, q3⟩ := slfRec_words (cc := c₂) (w3 h)
    have e1 : c₂.nreg (a1F + 1) = c.nreg (a1F + 1) :=
      c2r _ (by ufo a1F slfX sw) (by ufo a1F gRC sw) (by ufo a1F slfDc sw)
    have e2 : c₂.nreg (a1F + 2) = c.nreg (a1F + 2) :=
      c2r _ (by ufo a1F slfX sw) (by ufo a1F gRC sw) (by ufo a1F slfDc sw)
    have g : ∀ q, (q = oKd ∨ q = oKk ∨ q = oB ∨ q = slfA ∨ q = slfN ∨ q = slfL0 ∨ q = slfL1 ∨
        q = oPar) → c₂.nreg q = c.nreg q := by
      intro q hq
      exact c2r q (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfX, sw] <;> omega)
        (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, gRC, sw] <;> omega)
        (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfDc, sw] <;> omega)
    rw [e1, e2, g oKd (by simp), g oKk (by simp), g oB (by simp)] at q1
    rw [c2Dc] at q2
    rw [g slfA (by simp), g slfN (by simp), g slfL0 (by simp), g slfL1 (by simp),
      g oPar (by simp)] at q3
    refine ⟨slfRawV hD (d := 1 - b) (by omega) A1 pt1 (hE1 h) pw1 (hax ⟨_, _, A1, hE1 h⟩) q1 q2 q3,
      q1⟩
  -- the post
  have hO0  := bit0.1
  have hO4  := bit1.1
  refine ⟨by rwo [g3, g2], by rw [g3, g2]; splao, fun i hi1 hi2 => ?_,
    fun _ p t hA hL => ?_, fun a ha hs => ?_, ?_, fun r hr hS hrA => ?_⟩
  · -- validity
    by_cases hlt : i < c₂.nreg gRC
    · have hE : c.nreg slfO ≠ 1 := by intro h; rwo [g2, ite_eq_left h] at hlt
      have hi : i = c.nreg gRC := by rwo [g2, ite_eq_right hE] at hlt
      rw [hi]; exact (rec0 hE).1
    · have hE : c.nreg (slfO + 4) ≠ 1 := by intro h; rwo [g3, ite_eq_left h] at hi2
      have hi : i = c₂.nreg gRC := by rwo [g3, ite_eq_right hE] at hi2
      rw [hi]; exact (rec1 hE).1
  · -- completeness
    rcases attach_two E.hP E.hNF₂ hD arr0 arr1 hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hE : c.nreg slfO ≠ 1 := fun h => absurd (hN0 h) (not_lt.2 hL)
      obtain ⟨-, hr⟩ := rec0 hE
      refine ⟨c.nreg gRC, le_rfl, by rw [g3, g2, ite_eq_right hE]; splao, ?_, ?_, ?_⟩
      · rw [hr]
      · rw [hr]
      · rw [hr]
    · have hE : c.nreg (slfO + 4) ≠ 1 := fun h => absurd (hN1 h) (not_lt.2 hL)
      obtain ⟨-, hr⟩ := rec1 hE
      refine ⟨c₂.nreg gRC, by rwo [g2], by rwo [g3, ite_eq_right hE], ?_, ?_, ?_⟩
      · rw [hr]
      · rw [hr]
      · rw [hr]
  · -- memory
    rw [m3 a (by rcases hs with h | h <;> [left; right] <;> rw [g2] <;> split_ifs <;> omega),
      m2 a (by rcases hs with h | h <;> [left; right] <;> omega)]
  · -- the allocator
    rw [r3 _ (by ufo ALLOC slfX sw) (by ufo ALLOC gRC sw),
      c2r _ (by ufo ALLOC slfX sw) (by ufo ALLOC gRC sw)
        (by ufo ALLOC slfDc sw)]
  · -- the registers
    have hS' : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ r = gRC ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
      (sw 4010 ≤ r ∧ r < sw 4200) ∨ (sw 5000 ≤ r ∧ r < sw 6000)) := hS
    have a1 : r ≠ slfX := by intro h; apply hS'; subst h; ufo slfX sw
    have a2 : r ≠ gRC := fun h => hS' (Or.inr (Or.inl h))
    have a3 : r ≠ slfDc := by intro h; apply hS'; subst h; ufo slfDc sw
    rw [r3 r a1 a2, c2r r a1 a2 a3]

end

end SweepEv

end Chazelle.Core
