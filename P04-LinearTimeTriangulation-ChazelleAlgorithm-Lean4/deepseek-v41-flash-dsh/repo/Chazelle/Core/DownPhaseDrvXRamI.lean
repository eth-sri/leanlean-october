module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXRamH

/-!
# Down phase, extraction (D6), RAM part 9: one chord record

`chS_exec`: one chord record of `N_R`: if it is kept (`kR`), its interior triple and the buckets of
its two ends are stored at the current output positions (`stMem`); the chord pointer advances.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)

@[expose] public section

section ch

variable {P : Polygon} {W : ℕ} {v : XV} {N NR : NF} {ras : ℕ → ℕ} {A0 : ℕ} {mem0 : ℕ → ℕ}


open Classical in
/-- **One chord record of `N_R`.** -/
theorem chS_exec (E : XE P W v N NR ras A0 mem0) (d : Config) (hw : WordsBounded W d)
    (hmem : ∀ a, a < A0 → d.nmem a = mem0 a) (hg : XG P v d) {i cnt : ℕ}
    (hi : i < v.K) (hcnt : cnt ≤ i) (h39 : d.nreg 217039 = i) (h40 : d.nreg 217040 = v.CB + 5 * i)
    (h38 : d.nreg 217038 = cnt) (h45 : d.nreg 217045 = v.LxB + 3 * cnt)
    (h46 : d.nreg 217046 = v.BkB + 2 * cnt) :
    ∃ d' k, Exec P W chS d d' k ∧ k ≤ 24000 ∧
      d'.nreg 217039 = i + 1 ∧ d'.nreg 217040 = v.CB + 5 * (i + 1) ∧
      (kR P v (NR.chord i) → d'.nmem = stMem P v N d.nmem cnt (NR.chord i) ∧
        d'.nreg 217038 = cnt + 1 ∧ d'.nreg 217045 = v.LxB + 3 * (cnt + 1) ∧
        d'.nreg 217046 = v.BkB + 2 * (cnt + 1)) ∧
      (¬ kR P v (NR.chord i) → d'.nmem = d.nmem ∧ d'.nreg 217038 = cnt ∧
        d'.nreg 217045 = v.LxB + 3 * cnt ∧ d'.nreg 217046 = v.BkB + 2 * cnt) ∧
      FrameM Bch d d' := by
  have hA0W : A0 ≤ W := by have := E.hA0; omega
  have hHBW : v.HB + 3 * v.H.length + 1 ≤ W := by have := E.hHB; omega
  have hnW : (Qof P).n ≤ W := by have := E.hW; omega
  have hn0 : 0 < (Qof P).n := by have := E.hn2; omega
  obtain ⟨hh1, hlp, hrp⟩ := E.hch i hi
  obtain ⟨mh, mlp, mrp⟩ := E.hNRm d.nmem hmem i hi
  have hCB := E.hCB i hi
  have hLx := E.hLx
  have hBk := E.hBk
  have hA0 := E.hA0
  -- step 1: read the record
  obtain ⟨d1, k1, e1, hk1, a50, a51, a52, a53, a60⟩ : ∃ d1 k1, Exec P W
      (block [.loadN 217050 217040, .addN 217104 217040 217027, .loadN 217051 217104,
        .addN 217104 217104 217027, .loadN 217052 217104, .addN 217053 217050 217027,
        .copyN 217060 217051]) d d1 k1 ∧ k1 ≤ 7 ∧
      d1.nreg 217050 = (NR.chord i).h ∧ d1.nreg 217051 = (NR.chord i).lp ∧
      d1.nreg 217052 = (NR.chord i).rp ∧ d1.nreg 217053 = (NR.chord i).h + 1 ∧
      d1.nreg 217060 = (NR.chord i).lp := by
    have k1' : ∀ a, a = v.CB + 5 * i + 1 → d.nmem a = (NR.chord i).lp := fun a ha => ha ▸ mlp
    have k2' : ∀ a, a = v.CB + 5 * i + 2 → d.nmem a = (NR.chord i).rp := fun a ha => ha ▸ mrp
    exec_block
    · config_simp; rw [h40, hg.r27]; omega
    · config_simp; rw [h40, hg.r27]; omega
    · config_simp; rw [h40, mh, hg.r27]; omega
    · refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h40, hg.r27]
      · exact mh
      · exact k1' _ (by omega)
      · exact k2' _ (by omega)
      · rw [mh]
      · exact k1' _ (by omega)
  have f1 : FrameB (fun r => decide ((217050 ≤ r ∧ r ≤ 217053) ∨ r = 217060 ∨ r = 217104)) d d1 :=
    exec_frameB e1 (by decide)
  have hw1 := e1.wb_right
  have g1 : XG P v d1 := hg.frameM (FrameB.toM f1) (by decide)
  have m1 := f1.2.2.1
  -- step 2: the left end
  obtain ⟨d2, k2, e2, hk2, bL, encL, f2⟩ := clsS_exec (P := P) d1 hw1 (n := (Qof P).n)
    (m := v.m) (T := v.T) (HB := v.HB) (h := (NR.chord i).h) (p := (NR.chord i).lp) (β := v.β)
    (li := v.li) (H := v.H) (E.hHost _ (fun a ha => by rw [m1]; exact hmem a ha)) E.hwf E.hlen
    hHBW E.hW E.hm1 E.hmp E.hT hlp g1.r20 g1.r21 g1.r22 g1.r25 g1.r26 g1.r27 g1.r34 g1.r35
    g1.r41 g1.r42 g1.r44 a50 a60
  have hw2 := e2.wb_right
  have g2 : XG P v d2 := g1.frameM (FrameB.toM f2) (by decide)
  -- step 3: save it
  obtain ⟨d3, k3, e3, hk3, a54, a55, a56, a57, b60⟩ : ∃ d3 k3, Exec P W
      (block [.copyN 217054 217064, .copyN 217055 217070, .copyN 217056 217071,
        .copyN 217057 217072, .copyN 217060 217052]) d2 d3 k3 ∧ k3 ≤ 5 ∧
      d3.nreg 217054 = d2.nreg 217064 ∧ d3.nreg 217055 = d2.nreg 217070 ∧
      d3.nreg 217056 = d2.nreg 217071 ∧ d3.nreg 217057 = d2.nreg 217072 ∧
      d3.nreg 217060 = d2.nreg 217052 := by
    exec_block
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
  have f3 : FrameB (fun r => decide ((217054 ≤ r ∧ r ≤ 217057) ∨ r = 217060)) d2 d3 :=
    exec_frameB e3 (by decide)
  have hw3 := e3.wb_right
  have g3 : XG P v d3 := g2.frameM (FrameB.toM f3) (by decide)
  have c50 : d3.nreg 217050 = (NR.chord i).h := by
    rw [f3.1 _ (by decide), f2.1 _ (by decide), a50]
  have c60 : d3.nreg 217060 = (NR.chord i).rp := by
    rw [b60, f2.1 _ (by decide), a52]
  have m3 : d3.nmem = d.nmem := by rw [f3.2.2.1, f2.2.2.1, m1]
  -- step 4: the right end
  obtain ⟨d4, k4, e4, hk4, bR, encR, f4⟩ := clsS_exec (P := P) d3 hw3 (n := (Qof P).n)
    (m := v.m) (T := v.T) (HB := v.HB) (h := (NR.chord i).h) (p := (NR.chord i).rp) (β := v.β)
    (li := v.li) (H := v.H) (E.hHost _ (fun a ha => by rw [m3]; exact hmem a ha)) E.hwf E.hlen
    hHBW E.hW E.hm1 E.hmp E.hT hrp g3.r20 g3.r21 g3.r22 g3.r25 g3.r26 g3.r27 g3.r34 g3.r35
    g3.r41 g3.r42 g3.r44 c50 c60
  have hw4 := e4.wb_right
  have g4 : XG P v d4 := g3.frameM (FrameB.toM f4) (by decide)
  have m4 : d4.nmem = d.nmem := by rw [f4.2.2.1, m3]
  have hbL : d4.nreg 217054 =
      if RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp then 1 else 0 := by
    rw [f4.1 _ (by decide), a54, bL]
  -- the registers kept from `d`
  have q4 : ∀ r, (r = 217038 ∨ r = 217039 ∨ r = 217040 ∨ r = 217045 ∨ r = 217046) →
      d4.nreg r = d.nreg r := fun r hr => by
    rw [f4.1 _ (by simp only [Bcls, decide_eq_false_iff_not]; omega),
      f3.1 _ (by simp only [decide_eq_false_iff_not]; omega),
      f2.1 _ (by simp only [Bcls, decide_eq_false_iff_not]; omega),
      f1.1 _ (by simp only [decide_eq_false_iff_not]; omega)]
  have c53 : d4.nreg 217053 = (NR.chord i).h + 1 := by
    rw [f4.1 _ (by decide), f3.1 _ (by decide), f2.1 _ (by decide), a53]
  have c50' : d4.nreg 217050 = (NR.chord i).h := by rw [f4.1 _ (by decide), c50]
  -- step 5: the kept test
  obtain ⟨d5, k5, e5, hk5, o5k, o5n, p39, p40⟩ : ∃ d5 k5, Exec P W
      (.ifLtN 217054 217027 (.ifLtN 217064 217027 .skip keptS) keptS) d4 d5 k5 ∧ k5 ≤ 19500 ∧
      (kR P v (NR.chord i) → d5.nmem = stMem P v N d.nmem cnt (NR.chord i) ∧
        d5.nreg 217038 = cnt + 1 ∧ d5.nreg 217045 = v.LxB + 3 * (cnt + 1) ∧
        d5.nreg 217046 = v.BkB + 2 * (cnt + 1)) ∧
      (¬ kR P v (NR.chord i) → d5.nmem = d.nmem ∧ d5.nreg 217038 = cnt ∧
        d5.nreg 217045 = v.LxB + 3 * cnt ∧ d5.nreg 217046 = v.BkB + 2 * cnt) ∧
      d5.nreg 217039 = i ∧ d5.nreg 217040 = v.CB + 5 * i := by
    by_cases hk : kR P v (NR.chord i)
    · obtain ⟨hxL, hxR, hexL, hexR⟩ := E.hkf i hi hk
      have hmpt := E.hmp
      have hsL : (sPt P v (NR.chord i).lp).Lt (Qof P).n :=
        hpt_lt E.hwf hn0 (by have := tK_le (T := v.T) v.β E.hm1 (NR.chord i).lp; omega)
      have hsR : (sPt P v (NR.chord i).rp).Lt (Qof P).n :=
        hpt_lt E.hwf hn0 (by have := tK_le (T := v.T) v.β E.hm1 (NR.chord i).rp; omega)
      have eL : EncV (d4.nreg 217055) (d4.nreg 217056) (d4.nreg 217057) (sPt P v (NR.chord i).lp) := by
        rw [f4.1 _ (by decide), f4.1 _ (by decide), f4.1 _ (by decide), a55, a56, a57]
        exact (enc_iff _ _).1 encL
      have hgood' : ∀ j, j < N.arcs.length → GoodPos (Qof P) (N.arc j).s ∧
          GoodPos (Qof P) (N.arc j).e := fun j hj => E.hgood j (E.hA ▸ hj)
      obtain ⟨d5, k5, e5, hk5, m5, c38, c45, c46, f5⟩ := keptS_exec (P := P) d4 hw4 E.hG E.hli E.hdh
        E.hn2 (N := N) (sL := sPt P v (NR.chord i).lp) (sR := sPt P v (NR.chord i).rp)
        (h := (NR.chord i).h) (LxB := v.LxB) (BkB := v.BkB) (cnt := cnt) (AB := v.AB) (RA := v.RA)
        (nRA := v.nRA) (ras := ras) hsL hsR eL encR hxL hxR hexL hexR hgood' E.hinc E.hnext
        E.hfree (fun j hj => E.hAm d4.nmem (fun a ha => by rw [m4]; exact hmem a ha) j (E.hA ▸ hj))
        (fun t ht => ⟨E.hRm d4.nmem (fun a ha => by rw [m4]; exact hmem a ha) t ht,
          by rw [E.hA]; exact E.hras t ht⟩)
        (fun j hj => by have := E.hAW j (E.hA ▸ hj); omega) (by have := E.hRW; omega)
        (by rw [E.hA]; exact E.hA2) hnW g4.r20 g4.r26 g4.r27 (g4.r30.trans E.hA.symm) g4.r31
        g4.r32 g4.r33 g4.r44 c50' c53 (by rw [q4 _ (by omega), h38])
        (by rw [q4 _ (by omega), h45]) (by rw [q4 _ (by omega), h46])
        (by have := E.hK; omega) (by have := E.hK; omega) (by have := E.hK; omega)
      have p39 : d5.nreg 217039 = i := by
        rw [f5.1 _ (by decide), q4 _ (by omega), h39]
      have p40 : d5.nreg 217040 = v.CB + 5 * i := by
        rw [f5.1 _ (by decide), q4 _ (by omega), h40]
      have out : d5.nmem = stMem P v N d.nmem cnt (NR.chord i) := by
        rw [m5, m4]; rfl
      have hk5' : k5 ≤ 19448 := by have := E.hnRA; omega
      have hk' : RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp ∨
          RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).rp := hk
      by_cases hl : RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp
      · exact ⟨d5, k5 + 2, .ifLtN_false (by rw [hbL, ite_eq_left hl, g4.r27]; omega) e5, by omega,
          fun _ => ⟨out, c38, c45, c46⟩, fun h => absurd hk h, p39, p40⟩
      · have hr := hk'.resolve_left hl
        exact ⟨d5, k5 + 2 + 1, .ifLtN_true (by rw [hbL, ite_eq_right hl, g4.r27]; omega)
          (.ifLtN_false (by rw [bR, ite_eq_left hr, g4.r27]; omega) e5), by omega,
          fun _ => ⟨out, c38, c45, c46⟩, fun h => absurd hk h, p39, p40⟩
    · have hl : ¬ RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp :=
        fun h => hk (Or.inl h)
      have hr : ¬ RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).rp :=
        fun h => hk (Or.inr h)
      exact ⟨d4, 0 + 1 + 1, .ifLtN_true (by rw [hbL, ite_eq_right hl, g4.r27]; omega)
        (.ifLtN_true (by rw [bR, ite_eq_right hr, g4.r27]; omega) (.skip hw4)), by omega,
        fun h => absurd h hk, fun _ => ⟨m4, by rw [q4 _ (by omega), h38],
          by rw [q4 _ (by omega), h45], by rw [q4 _ (by omega), h46]⟩,
        by rw [q4 _ (by omega), h39], by rw [q4 _ (by omega), h40]⟩
  have hw5 := e5.wb_right
  have g5 : XG P v d5 := g4.frameM (exec_frameM e5 (B := Bch) (by decide)) (by decide)
  -- step 6: advance
  obtain ⟨d6, k6, e6, hk6, w39, w40, w38, w45, w46⟩ : ∃ d6 k6, Exec P W
      (block [.addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217040 217040 217027,
        .addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217039 217039 217027])
      d5 d6 k6 ∧ k6 ≤ 6 ∧ d6.nreg 217039 = i + 1 ∧ d6.nreg 217040 = v.CB + 5 * (i + 1) ∧
      d6.nreg 217038 = d5.nreg 217038 ∧ d6.nreg 217045 = d5.nreg 217045 ∧
      d6.nreg 217046 = d5.nreg 217046 := by
    have r27 := g5.r27
    exec_block
    all_goals (try (config_simp; omega))
  have f6 : FrameB (fun r => decide (r = 217039 ∨ r = 217040)) d5 d6 := exec_frameB e6 (by decide)
  have ex : Exec P W chS d d6 (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) := by
    simp only [chS, seqs_cons₂, seqs_one]
    exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6))))
  have hk : k1 + (k2 + (k3 + (k4 + (k5 + k6)))) ≤ 24000 := by omega
  refine ⟨d6, _, ex, hk, w39, w40, fun hk => ?_, fun hk => ?_, exec_frameM ex wrM_ch⟩
  · obtain ⟨o1, o2, o3, o4⟩ := o5k hk
    exact ⟨by rw [f6.2.2.1, o1], by rw [w38, o2], by rw [w45, o3], by rw [w46, o4]⟩
  · obtain ⟨o1, o2, o3, o4⟩ := o5n hk
    exact ⟨by rw [f6.2.2.1, o1], by rw [w38, o2], by rw [w45, o3], by rw [w46, o4]⟩

end ch

end

end DrvX

end Chazelle.Core
