module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvHArc
public import Chazelle.Core.DownPhaseDrvXPos2
public import Chazelle.Core.DownPhaseDrvXKept
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.ShotListCut
public import Chazelle.Core.NFDecompBfs

namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)
@[expose] public section
structure XV where
  m : ℕ
  T : ℕ
  β : Bool
  li : Bool
  H : Host
  HB : ℕ
  K : ℕ
  CB : ℕ
  A : ℕ
  AB : ℕ
  nRA : ℕ
  RA : ℕ
  LxB : ℕ
  BkB : ℕ

/-- **The global registers.** -/
structure XG (P : Polygon) (v : XV) (d : Config) : Prop where
  r20 : d.nreg 217020 = (Qof P).n
  r21 : d.nreg 217021 = v.m
  r22 : d.nreg 217022 = 2 * v.m
  r25 : d.nreg 217025 = tS v.m v.T v.β
  r26 : d.nreg 217026 = liV v.li
  r27 : d.nreg 217027 = 1
  r28 : d.nreg 217028 = v.K
  r30 : d.nreg 217030 = v.A
  r31 : d.nreg 217031 = v.AB
  r32 : d.nreg 217032 = v.nRA
  r33 : d.nreg 217033 = v.RA
  r34 : d.nreg 217034 = v.H.length
  r35 : d.nreg 217035 = v.HB + 1
  r36 : d.nreg 217036 = v.LxB
  r37 : d.nreg 217037 = v.BkB
  r41 : d.nreg 217041 = 6
  r42 : d.nreg 217042 = 2 * v.m + 6
  r44 : d.nreg 217044 = 2

/-- The global registers. -/
def xgRegs : List ℕ := [217020, 217021, 217022, 217025, 217026, 217027, 217028, 217030, 217031,
  217032, 217033, 217034, 217035, 217036, 217037, 217041, 217042, 217044]
variable {P : Polygon} {v : XV} {d d' : Config}
theorem XG.congr (h : XG P v d)
    (hr : ∀ r ∈ xgRegs, d'.nreg r = d.nreg r) : XG P v d' :=
  ⟨(hr _ by_decide).trans h.r20, (hr _ by_decide).trans h.r21,
    (hr _ by_decide).trans h.r22, (hr _ by_decide).trans h.r25,
    (hr _ by_decide).trans h.r26, (hr _ by_decide).trans h.r27,
    (hr _ by_decide).trans h.r28, (hr _ by_decide).trans h.r30,
    (hr _ by_decide).trans h.r31, (hr _ by_decide).trans h.r32,
    (hr _ by_decide).trans h.r33, (hr _ by_decide).trans h.r34,
    (hr _ by_decide).trans h.r35, (hr _ by_decide).trans h.r36,
    (hr _ by_decide).trans h.r37, (hr _ by_decide).trans h.r41,
    (hr _ by_decide).trans h.r42, (hr _ by_decide).trans h.r44⟩
theorem XG.frameM {B : ℕ → Bool} (h : XG P v d)
    (hf : FrameM B d d') (hB : xgRegs.all (fun r => !B r) = true) : XG P v d' :=
  h.congr fun r hr => hf.1 r (by
    simp_all)

/-- The interior walk position of an end, from the values of a run. -/
noncomputable def xP (P : Polygon) (v : XV) (h p : ℕ) : WPos := xPos (Qof P).n v.H v.li v.m v.T v.β h p

/-- The kept test, from the values of a run. -/
def kR (P : Polygon) (v : XV) (c : CRec) : Prop :=
  KeptT (Qof P).n v.H v.li v.m v.T v.β c.h c.lp c.rp
noncomputable instance (P : Polygon) (v : XV) (c : CRec) : Decidable (kR P v c) := by
  unfold kR; infer_instance

/-- **The facts of a run** (`N` the interior normal form, `NR` the normal form of the region
chain, `ras` the arc list of the region, memory `mem0` below `A0`). -/
structure XE (P : Polygon) (W : ℕ) (v : XV) (N NR : NF) (ras : ℕ → ℕ) (A0 : ℕ)
    (mem0 : ℕ → ℕ) : Prop where
  hG : GoodEnv P
  hli : v.li = true ↔ Mountain.LeftInside zta
  hdh : DistinctHeights zta
  hn2 : 2 ≤ (Qof P).n
  hW : 256 * (Qof P).n + 16 ≤ W
  hK : NR.chords.length = v.K
  hA0 : A0 + 5 * v.K ≤ W
  hHost : ∀ mm : ℕ → ℕ, ztcqd → HostAt mm v.HB v.H
  hwf : HostWF (Qof P).n v.H
  hlen : v.H.length ≤ 64
  hHB : v.HB + 3 * v.H.length + 1 ≤ A0
  hm1 : 1 ≤ v.m
  hmp : v.m + 1 = (v.H.pts (Qof P).n).length
  hT : v.T ≤ v.m
  hNRm : ∀ mm : ℕ → ℕ, ztcqd → ∀ i, i < v.K →
    mm (v.CB + 5 * i) = (NR.chord i).h ∧ mm (v.CB + 5 * i + 1) = (NR.chord i).lp ∧
      mm (v.CB + 5 * i + 2) = (NR.chord i).rp
  hCB : ∀ i, i < v.K → v.CB + 5 * i + 4 < A0
  hch : ∀ i, i < v.K → (NR.chord i).h + 1 ≤ (Qof P).n ∧ (NR.chord i).lp ≤ 2 * v.m + 6 ∧
    (NR.chord i).rp ≤ 2 * v.m + 6
  hA : N.arcs.length = v.A
  hgood : ∀ j, j < v.A → GoodPos zta (N.arc j).s ∧ GoodPos zta (N.arc j).e
  hinc : ∀ j j', j < j' → j' < N.arcs.length →
    (interiorModel zta).key zta (N.arc j).s <
      (interiorModel zta).key zta (N.arc j').s
  hnext : ∀ j, j < N.arcs.length →
    (interiorModel zta).key zta (N.arc j).e =
      (interiorModel zta).key zta (N.arc ztbaaq).s
  hfree : ∀ j j', j < N.arcs.length → j' < N.arcs.length →
    ¬ sideInArc ztwzc
      ztwzb
      ztxtv
  hAm : ∀ mm : ℕ → ℕ, ztcqd → ∀ j, j < v.A →
    mm (v.AB + 5 * j + 1) = (N.arc j).s.edge ∧ mm (v.AB + 5 * j + 2) = (N.arc j).s.hgt ∧
      mm (v.AB + 5 * j + 3) = (N.arc j).e.edge ∧ mm (v.AB + 5 * j + 4) = (N.arc j).e.hgt
  hRm : ∀ mm : ℕ → ℕ, ztcqd → ∀ t, t < v.nRA → mm (v.RA + t) = ras t
  hras : ∀ t, t < v.nRA → ras t < v.A
  hAW : ∀ j, j < v.A → v.AB + 5 * j + 4 < A0
  hRW : v.RA + v.nRA ≤ A0
  hnRA : v.nRA ≤ 32
  hA2 : 2 * v.A + 2 ≤ W
  hkf : ∀ i, i < v.K → kR P v ztctl →
    GoodPos zta ztimj ∧
    GoodPos zta ztimk ∧
    (∃ t, t < v.nRA ∧ OnArcP zta v.li N ztcdn ztimj) ∧
    (∃ t, t < v.nRA ∧ OnArcP zta v.li N ztcdn ztimk)
  hLx : v.LxB = A0
  hBk : v.BkB = A0 + 3 * v.K

/-- The registers `chS` writes. -/
def Bch (r : ℕ) : Bool :=
  decide ((217038 ≤ r ∧ r ≤ 217040) ∨ (217045 ≤ r ∧ r ≤ 217046) ∨ (217050 ≤ r ∧ r ≤ 217199))
theorem wrM_ch : wrM Bch chS = true := by_decide

/-- The host point at the start of walk edge `p`. -/
noncomputable def sPt (P : Polygon) (v : XV) (p : ℕ) : SymPt := hpt (Qof P).n v.H (tK v.m v.T v.β p)

/-- The memory after storing a kept chord. -/
noncomputable def stMem (P : Polygon) (v : XV) (N : NF) (mm : ℕ → ℕ) (cnt : ℕ) (c : CRec) : ℕ → ℕ :=
  upd (upd (upd (upd (upd mm (v.LxB + 3 * cnt) c.h) (v.LxB + 3 * cnt + 1)
    (xP P v c.h c.lp).edge) (v.LxB + 3 * cnt + 2) (xP P v c.h c.rp).edge) (v.BkB + 2 * cnt)
      (keyBkt zta N ztqzc)) (v.BkB + 2 * cnt + 1)
      (keyBkt zta N ztqzd)
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)
@[expose] public section
section ch
variable {P : Polygon} {W : ℕ} {v : XV} {N NR : NF} {ras : ℕ → ℕ} {A0 : ℕ} {mem0 : ℕ → ℕ}
set_option maxHeartbeats 8000000 in
open Classical in
/-- **One chord record of `N_R`.** -/
theorem chS_exec (E : XE P W v N NR ras A0 mem0) (d : Config) (hw : WordsBounded W d)
    (hmem : ∀ a, a < A0 → d.nmem a = mem0 a) (hg : XG P v d) {i cnt : ℕ}
    (hi : i < v.K) (hcnt : cnt ≤ i) (h39 : d.nreg 217039 = i) (h40 : d.nreg 217040 = v.CB + 5 * i)
    (h38 : d.nreg 217038 = cnt) (h45 : d.nreg 217045 = v.LxB + 3 * cnt)
    (h46 : d.nreg 217046 = v.BkB + 2 * cnt) :
    ∃ d' k, Exec P W chS d d' k ∧ k ≤ 24000 ∧
      d'.nreg 217039 = i + 1 ∧ d'.nreg 217040 = v.CB + 5 * ztg ∧
      (kR P v ztctl → d'.nmem = stMem P v N d.nmem cnt ztctl ∧
        d'.nreg 217038 = cnt + 1 ∧ d'.nreg 217045 = v.LxB + 3 * ztbzu ∧
        d'.nreg 217046 = v.BkB + 2 * ztbzu) ∧
      (¬ kR P v ztctl → d'.nmem = d.nmem ∧ d'.nreg 217038 = cnt ∧
        d'.nreg 217045 = v.LxB + 3 * cnt ∧ d'.nreg 217046 = v.BkB + 2 * cnt) ∧
      FrameM Bch d d' := by
  have hA0W : A0 ≤ W := by have := E.hA0; omega
  have hHBW : v.HB + 3 * v.H.length + 1 ≤ W := by have := E.hHB; omega
  have hnW : (Qof P).n ≤ W := by have := E.hW; omega
  have hn0 : ztfzz := by have := E.hn2; omega
  obtain ⟨hh1, hlp, hrp⟩ := E.hch i hi
  obtain ⟨mh, mlp, mrp⟩ := E.hNRm d.nmem hmem i hi
  have hCB := E.hCB i hi
  zuhxa

  zumbi
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
    · refine ztbfj <;> config_simp <;> simp only [h40, hg.r27]
      · exact mh
      · omega
      · omega
      · rw [mh]
      omega
  have f1 : FrameB (fun r => decide ((217050 ≤ r ∧ r ≤ 217053) ∨ r = 217060 ∨ r = 217104)) d d1 :=
    exec_frameB e1 by_decide
  zuqj
  have g1 : ztumo := hg.frameM (FrameB.toM f1) by_decide
  have m1 : d1.nmem = d.nmem := f1.2.2.1
  -- step 2: the left end
  obtain ⟨d2, k2, e2, hk2, bL, encL, f2⟩ := clsS_exec (P := P) d1 hw1 (n := (Qof P).n)
    (m := v.m) (T := v.T) (HB := v.HB) (h := (NR.chord i).h) (p := (NR.chord i).lp) (β := v.β)
    (li := v.li) (H := v.H) ztztk E.hwf E.hlen
    hHBW E.hW E.hm1 E.hmp E.hT hlp g1.r20 g1.r21 g1.r22 g1.r25 g1.r26 g1.r27 g1.r34 g1.r35
    g1.r41 g1.r42 g1.r44 a50 a60
  zump
  have g2 : ztump := g1.frameM (FrameB.toM f2) by_decide
  -- step 3: save it
  obtain ⟨d3, k3, e3, hk3, a54, a55, a56, a57, b60⟩ : ∃ d3 k3, Exec P W
      (block [.copyN 217054 217064, .copyN 217055 217070, .copyN 217056 217071,
        .copyN 217057 217072, .copyN 217060 217052]) d2 d3 k3 ∧ k3 ≤ 5 ∧
      d3.nreg 217054 = d2.nreg 217064 ∧ d3.nreg 217055 = d2.nreg 217070 ∧
      d3.nreg 217056 = d2.nreg 217071 ∧ d3.nreg 217057 = d2.nreg 217072 ∧
      d3.nreg 217060 = d2.nreg 217052 := by
    exec_block
    simp
  have f3 : FrameB (fun r => decide ((217054 ≤ r ∧ r ≤ 217057) ∨ r = 217060)) d2 d3 :=
    exec_frameB e3 by_decide
  zubgh
  have g3 : XG P v d3 := g2.frameM (FrameB.toM f3) by_decide
  have c50 : d3.nreg 217050 = (NR.chord i).h := by
    rw [f3.1 _ by_decide, f2.1 _ by_decide, a50]
  have c60 : d3.nreg 217060 = (NR.chord i).rp := by
    rw [b60, f2.1 _ by_decide, a52]
  have m3 : d3.nmem = d.nmem := by zunyl
  -- step 4: the right end
  obtain ⟨d4, k4, e4, hk4, bR, encR, f4⟩ := clsS_exec (P := P) d3 hw3 (n := (Qof P).n)
    (m := v.m) (T := v.T) (HB := v.HB) (h := (NR.chord i).h) (p := (NR.chord i).rp) (β := v.β)
    (li := v.li) (H := v.H) ztztk E.hwf E.hlen
    hHBW E.hW E.hm1 E.hmp E.hT hrp g3.r20 g3.r21 g3.r22 g3.r25 g3.r26 g3.r27 g3.r34 g3.r35
    g3.r41 g3.r42 g3.r44 c50 c60
  zubgi
  have g4 : XG P v d4 := g3.frameM (FrameB.toM f4) by_decide
  have m4 : d4.nmem = d.nmem := by rw [f4.2.2.1, m3]
  have hbL : d4.nreg 217054 =
      if RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp then 1 else 0 := by
    rw [f4.1 _ by_decide, a54, bL]
  -- the registers kept from `d`
  have q4 : ∀ r, (r = 217038 ∨ r = 217039 ∨ r = 217040 ∨ r = 217045 ∨ r = 217046) →
      d4.nreg r = d.nreg r := fun r hr => by
    rw [f4.1 _ ztkuu,
      f3.1 _ by_grind,
      f2.1 _ ztkuu,
      f1.1 _ by_grind]
  have c53 : d4.nreg 217053 = (NR.chord i).h + 1 := by
    rw [f4.1 _ by_decide, f3.1 _ by_decide, f2.1 _ by_decide, a53]
  have c50' : d4.nreg 217050 = (NR.chord i).h := by rw [f4.1 _ by_decide, c50]
  -- step 5: the kept test
  obtain ⟨d5, k5, e5, hk5, o5k, o5n, p39, p40⟩ : ∃ d5 k5, Exec P W
      (.ifLtN 217054 217027 ztprp keptS) d4 d5 k5 ∧ k5 ≤ 19500 ∧
      (kR P v ztctl → d5.nmem = stMem P v N d.nmem cnt ztctl ∧
        d5.nreg 217038 = cnt + 1 ∧ d5.nreg 217045 = v.LxB + 3 * ztbzu ∧
        d5.nreg 217046 = v.BkB + 2 * ztbzu) ∧
      (¬ kR P v ztctl → d5.nmem = d.nmem ∧ d5.nreg 217038 = cnt ∧
        d5.nreg 217045 = v.LxB + 3 * cnt ∧ d5.nreg 217046 = v.BkB + 2 * cnt) ∧
      d5.nreg 217039 = i ∧ d5.nreg 217040 = v.CB + 5 * i := by
    zuirr
    · obtain ⟨hxL, hxR, hexL, hexR⟩ := E.hkf i hi hk
      have hmpt := E.hmp
      have hsL : (sPt P v (NR.chord i).lp).Lt (Qof P).n :=
        hpt_lt E.hwf hn0 (by have := tK_le (T := v.T) v.β E.hm1 (NR.chord i).lp; omega)
      have hsR : (sPt P v (NR.chord i).rp).Lt (Qof P).n :=
        hpt_lt E.hwf hn0 (by have := tK_le (T := v.T) v.β E.hm1 (NR.chord i).rp; omega)
      have eL : EncV (d4.nreg 217055) (d4.nreg 217056) (d4.nreg 217057) (sPt P v (NR.chord i).lp) := by
        rw [f4.1 _ by_decide, f4.1 _ by_decide, f4.1 _ by_decide, a55, a56, a57]
        exact (enc_iff _ _).1 encL
      have hgood' : ∀ j, j < N.arcs.length → GoodPos zta (N.arc j).s ∧
          GoodPos zta (N.arc j).e := fun j hj => E.hgood j ztnkv
      obtain ⟨d5, k5, e5, hk5, m5, c38, c45, c46, f5⟩ := keptS_exec (P := P) d4 hw4 E.hG E.hli E.hdh
        E.hn2 (N := N) (sL := sPt P v (NR.chord i).lp) (sR := sPt P v (NR.chord i).rp)
        (h := (NR.chord i).h) (LxB := v.LxB) (BkB := v.BkB) (cnt := cnt) (AB := v.AB) (RA := v.RA)
        (nRA := v.nRA) (ras := ras) hsL hsR eL encR hxL hxR hexL hexR hgood' E.hinc E.hnext
        E.hfree (fun j hj => E.hAm d4.nmem ztxl j ztnkv)
        (fun t ht => ⟨E.hRm d4.nmem ztxl t ht,
          by zuowl; exact E.hras t ht⟩)
        (fun j hj => by have := E.hAW j ztnkv; omega) (by have := E.hRW; omega)
        (by zuowl; exact E.hA2) hnW g4.r20 g4.r26 g4.r27 (g4.r30.trans E.hA.symm) g4.r31
        g4.r32 g4.r33 g4.r44 c50' c53 by_grind
        by_grind by_grind
        by_omega by_omega by_omega
      have p39 : d5.nreg 217039 = i := by
        rw [f5.1 _ by_decide, q4 _ by_omega, h39]
      have p40 : d5.nreg 217040 = v.CB + 5 * i := by
        rw [f5.1 _ by_decide, q4 _ by_omega, h40]
      have out : d5.nmem = stMem P v N d.nmem cnt ztctl := by
        zuojq; rfl
      have hk5' : k5 ≤ 19448 := by have := E.hnRA; omega
      have hk' : RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp ∨
          RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).rp := hk
      by_cases hl : RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp
      · exact ⟨d5, k5 + 2, .ifLtN_false (by rw [hbL, ite_eq_left hl, g4.r27]; omega) e5, by_omega,
          fun _ => ztooz, fun h => absurd hk h, p39, p40⟩
      · have hr := hk'.resolve_left hl
        exact ⟨d5, k5 + 2 + 1, .ifLtN_true ztirr
          (.ifLtN_false (by rw [bR, ite_eq_left hr, g4.r27]; omega) e5), by_omega,
          fun _ => ztooz, fun h => absurd hk h, p39, p40⟩
    · have hl : ¬ RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).lp :=
        fun h => hk zteg
      have hr : ¬ RegIn (Qof P).n v.H v.li v.m v.T v.β (NR.chord i).h (NR.chord i).rp :=
        fun h => hk ztbho
      exact ⟨d4, 0 + 1 + 1, .ifLtN_true ztirr
        (.ifLtN_true (by rw [bR, ite_eq_right hr, g4.r27]; omega) ztpsa), by_omega,
        fun h => absurd h hk, fun _ => ⟨m4, by_simp_all,
          by simp_all, by_simp_all⟩,
        by simp_all, by_simp_all⟩
  zudpn
  have g5 : XG P v d5 := g4.frameM (exec_frameM e5 (B := Bch) by_decide) by_decide
  -- step 6: advance
  obtain ⟨d6, k6, e6, hk6, w39, w40, w38, w45, w46⟩ : ∃ d6 k6, Exec P W
      (block [.addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217040 217040 217027,
        .addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217039 217039 217027])
      d5 d6 k6 ∧ k6 ≤ 6 ∧ d6.nreg 217039 = i + 1 ∧ d6.nreg 217040 = v.CB + 5 * ztg ∧
      d6.nreg 217038 = d5.nreg 217038 ∧ d6.nreg 217045 = d5.nreg 217045 ∧
      d6.nreg 217046 = d5.nreg 217046 := by
    have r27 := g5.r27
    exec_block
    all_goals (try (config_simp; omega))
  have f6 : FrameB (fun r => decide (r = 217039 ∨ r = 217040)) d5 d6 := exec_frameB e6 by_decide
  have ex : Exec P W chS d d6 (k1 + ztrd) := by
    simp only [chS, seqs_cons₂, seqs_one]
    exact .seq e1 ztvb
  have hk : k1 + ztrd ≤ 24000 := by_omega
  refine ⟨d6, _, ex, hk, w39, w40, fun hk => ?_, fun hk => ?_, exec_frameM ex wrM_ch⟩
  · obtain ⟨o1, o2, o3, o4⟩ := o5k hk
    exact ztinm
  · obtain ⟨o1, o2, o3, o4⟩ := o5n hk
    exact ztinm
end ch
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE keyBkt endPos)
@[expose] public section
noncomputable def kl (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : List ℕ :=
  (List.range i).filter fun t => decide (kR P v ztqaj)

/-- The interior triple of chord record `t`. -/
noncomputable def xT (P : Polygon) (v : XV) (NR : NF) (t : ℕ) : ℕ × ℕ × ℕ :=
  xTriple (Qof P).n v.H v.li v.m v.T v.β (NR.chord t).h (NR.chord t).lp (NR.chord t).rp

/-- **The triples of the kept records** among the first `i`. -/
noncomputable def xL (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : List zte :=
  (kl P v NR i).map (xT P v NR)
theorem kl_succ (P : Polygon) (v : XV) (NR : NF) (i : ℕ) :
    kl P v NR ztg = kl P v NR i ++ (if kR P v ztctl then [i] else []) := by
  unfold kl
  zubic
theorem xL_kept {P : Polygon} {v : XV} {NR : NF} {i : ℕ} (h : kR P v ztctl) :
    xL P v NR ztg = xL P v NR i ++ [xT P v NR i] := by
  unfold xL; rw [kl_succ, ite_eq_left h, List.map_append]; rfl
theorem xL_not {P : Polygon} {v : XV} {NR : NF} {i : ℕ} (h : ¬ kR P v ztctl) :
    xL P v NR ztg = xL P v NR i := by
  unfold xL; rw [kl_succ, ite_eq_right h, List.append_nil]
theorem xL_length_le (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : (xL P v NR i).length ≤ i := by
  unfold xL kl
  grind
theorem endPos_append {L M : List zte} {q : ℕ} (hq : q < 2 * L.length) :
    endPos (L ++ M) q = endPos L q := by
  zuiqc
  grind
variable (L : List (ℕ × ℕ × ℕ)) (x : ℕ × ℕ × ℕ)
theorem endPos_last_l :
    endPos ztffm ztpu = (recOf x).lpos := by
  zuiqc
  simp
theorem endPos_last_r :
    endPos ztffm (2 * L.length + 1) = (recOf x).rpos := by
  zuiqc
  grind
theorem stMem_apply (P : Polygon) (v : XV) (N : NF) (mm : ℕ → ℕ) (cnt : ℕ) (c : CRec) (a : ℕ) :
    stMem P v N mm cnt c a =
      if a = v.BkB + 2 * cnt + 1 then keyBkt zta N ztqzd
      else if a = v.BkB + 2 * cnt then keyBkt zta N ztqzc
      else if a = v.LxB + 3 * cnt + 2 then (xP P v c.h c.rp).edge
      else if a = v.LxB + 3 * cnt + 1 then (xP P v c.h c.lp).edge
      else if a = v.LxB + 3 * cnt then c.h else mm a := by
  rfl
section loop
variable {P : Polygon} {W : ℕ} {v : XV} {N NR : NF} {ras : ℕ → ℕ} {A0 : ℕ} {mem0 : ℕ → ℕ}
set_option maxHeartbeats 8000000 in
/-- **The loop over the chord records.** -/
theorem loopS_exec (E : XE P W v N NR ras A0 mem0) (d : Config) (hw : WordsBounded W d)
    (hmem : ∀ a, a < A0 → d.nmem a = mem0 a) (hg : XG P v d) (h39 : d.nreg 217039 = 0)
    (h40 : d.nreg 217040 = v.CB) (h38 : d.nreg 217038 = 0) (h45 : d.nreg 217045 = v.LxB)
    (h46 : d.nreg 217046 = v.BkB) :
    ∃ d' k, Exec P W loopS d d' k ∧ k ≤ 24002 * v.K + 2 ∧ XG P v d' ∧
      d'.nreg 217038 = (xL P v NR v.K).length ∧ (∀ a, a < A0 → d'.nmem a = mem0 a) ∧
      ChordListAt d'.nmem v.LxB ztqzb ∧
      (∀ q, q < 2 * (xL P v NR v.K).length →
        d'.nmem ztucw = keyBkt zta N (endPos ztqzb q)) ∧
      FrameM Bch d d' := by
  zuhxa

  let Inv : ℕ → Config → Prop := fun i c => WordsBounded W c ∧ c.nreg 217039 = i ∧
    c.nreg 217028 = v.K ∧ XG P v c ∧ c.nreg 217040 = v.CB + 5 * i ∧
    c.nreg 217038 = (xL P v NR i).length ∧ c.nreg 217045 = v.LxB + 3 * (xL P v NR i).length ∧
    c.nreg 217046 = v.BkB + 2 * (xL P v NR i).length ∧ (∀ a, a < A0 → c.nmem a = mem0 a) ∧
    ChordListAt c.nmem v.LxB ztqza ∧
    (∀ q, q < 2 * (xL P v NR i).length →
      c.nmem ztucw = keyBkt zta N (endPos ztqza q)) ∧ FrameM Bch d c
  have hI0 : Inv 0 d := ⟨hw, h39, hg.r28, hg, by_omega,
    by tauto, by_tauto, by_tauto, hmem,
    fun q hq => by_tauto, fun q hq => by_tauto, FrameM.refl _ _⟩
  obtain ⟨d', k', e', ⟨-, -, -, g', -, c38, -, -, cm, cl, cb, f'⟩, hk'⟩ := DrvR.forLoop (P := P)
    (W := W) (ir := 217039) (nr := 217028) (body := chS) Inv 24000 v.K
    (fun i c hc => ztklj)
    (fun i c hi hc => by
      obtain ⟨hwc, c39, c28, cg, c40, c38, c45, c46, cmem, clist, cbkt, cf⟩ := hc
      have hlen := xL_length_le P v NR i
      obtain ⟨c', kc, ec, hkc, b39, b40, bk, bn, bf⟩ := chS_exec E c hwc cmem cg hi hlen c39 c40
        c38 c45 c46
      have cg' : XG P v c' := cg.frameM bf by_decide
      refine ⟨c', kc, ec, ⟨ec.wb_right, b39, by rw [bf.1 _ by_decide, c28], cg', b40, ?_⟩, hkc⟩
      zuirr
      · obtain ⟨m', d38, d45, d46⟩ := bk hk
        rw [xL_kept hk]
        simp only [List.length_append, List.length_singleton]
        zumbu
        zumbi
        refine ⟨d38, d45, d46, fun a ha => ?_, fun q hq => ?_, fun q hq => ?_, cf.trans bf⟩
        · rw [m', stMem_apply]
          grind
        · zugwb
          simp only [List.length_append, List.length_singleton] at hq
          rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq' | hq'
          · rw [List.getD_append _ _ _ _ hq']
            obtain ⟨x1, x2, x3⟩ := clist q hq'
            zusk
            · zugfk
            · zugfk
            · zugfk
          · subst hq'
            rw [List.getD_append_right _ _ _ _ ztbhw, Nat.sub_self]
            zusk
            · zucer
            · zucer
            · zucer
        · zugwb
          by_cases hq' : q < 2 * (xL P v NR i).length
          · rw [endPos_append hq', ← cbkt q hq', stMem_apply]
            grind
          · rcases (show q = 2 * (xL P v NR i).length ∨ q = 2 * (xL P v NR i).length + 1 by omega)
              with hq'' | hq''
            · subst hq''
              rw [endPos_last_l, stMem_apply]
              zufcy
            · subst hq''
              rw [endPos_last_r, stMem_apply]
              zufcy
      · obtain ⟨m', d38, d45, d46⟩ := bn hk
        rw [xL_not hk]
        exact ⟨d38, d45, d46, fun a ha => by_simp_all, by_simp_all,
          fun q hq => by_simp_all, cf.trans bf⟩)
    hI0 ztbg
  have hk : k' ≤ 24002 * v.K + 2 := by
    omega
  exact ⟨d', k', e', hk, g', c38, cm, cl, cb, f'⟩
end loop
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine BuildNF
open DrvR (regHost keyBkt OnArcKey endPos)
@[expose] public section
def xKappa : ℕ := 24100

/-- **The values of the run** read off the configuration `c` and the objects of the
precondition. -/
noncomputable def xvOf (P : Polygon) (c : Config) (C : Chain) (N NR : NF) : XV where
  m := C.m
  T := C.topIdx
  β := C.sideBeta
  li := decide ztlks
  H := regHost ztgm (Qof P).n N ztos
  HB := c.nreg 217003
  K := NR.chords.length
  CB := c.nmem ztrly
  A := N.arcs.length
  AB := c.nmem ztrlx
  nRA := (N.region ztos).arcs.length
  RA := c.nmem zthuo +
    c.nmem ztccq
  LxB := c.nreg ALLOC
  BkB := c.nreg ALLOC + 3 * NR.chords.length

/-- The arc list of region `r`. -/
def rasOf (N : NF) (r : ℕ) : ℕ → ℕ := fun t => (N.region r).arcs.getD t 0

/-- **The memory facts and bounds of the set-up** (`MD = 217005`, `HB = 217003`,
`BN = 217000`, `BR = 217006`, `r = 217001`, `RB = mem (BN + 5)`). -/
def SetupFacts (P : Polygon) (W : ℕ) (c : Config) (C : Chain) (N NR : NF) : Prop :=
  c.nmem (c.nreg 217005 + 3) = C.m ∧ c.nmem (c.nreg 217005 + 4) = C.topIdx ∧
    (c.nmem (c.nreg 217005 + 5) = 1 ↔ C.sideBeta = true) ∧
    c.nmem ztmga = (xvOf P c C N NR).H.length ∧
    c.nmem ztchk = NR.chords.length ∧
    c.nmem (c.nreg 217000 + 1) = N.arcs.length ∧
    c.nmem (c.nmem ztlkr + 5 * c.nreg 217001) =
      (N.region ztos).arcs.length ∧
    P.n ≤ W ∧ c.nreg 217005 + 5 ≤ W ∧ 2 * C.m + 6 ≤ W ∧ c.nreg 217003 + 1 ≤ W ∧
    c.nreg 217006 + 3 ≤ W ∧ c.nreg 217000 + 7 ≤ W ∧
    c.nmem ztlkr + 5 * c.nreg 217001 + 1 ≤ W ∧
    (xvOf P c C N NR).RA ≤ W ∧ 7 ≤ W

/-- **Glue A**: the facts of the run from the precondition of `DrvR.ExtractRamSpec`. -/
def XEGlue : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config) (L : List zte) (E : List ℕ) (C : Chain) (NR : NF),
    GoodEnv P → hostWords P.n ≤ W → c.nreg 217002 ≤ 1 →
    ztxkt → L ≠ [] →
    ChordTriplesOK ztwiq zta L → E.Perm ztct →
    E.Pairwise ztbajl →
    (interiorModel zta).DegLe
      ((BuildNF.buildNF ztwiq zta L E).F ztwiq zta) 4 →
    NFWithin c.nmem zthup ztm (BuildNF.buildNF ztwiq zta L E) →
    c.nreg 217001 < (BuildNF.buildNF ztwiq zta L E).nRegions →
    Robust ztm c.nmem (fun m => HostAt m ztmga
      (regHost ztgm (Qof P).n
        (BuildNF.buildNF ztwiq zta L E) ztos)) →
    c.nreg 217003 + 3 * (regHost ztgm (Qof P).n
        (BuildNF.buildNF ztwiq zta L E) ztos).length + 1 ≤
      c.nreg ALLOC →
    C.P = (regHost ztgm (Qof P).n
      (BuildNF.buildNF ztwiq zta L E) ztos).poly (Qof P) →
    C.s = 0 → C.m + 1 = C.P.n →
    ModelDescWF P ztm c.nmem ztghe →
    Robust ztm c.nmem (fun m => ModelDescAt m ztghe zta ztc) →
    Robust ztm c.nmem (fun m => ChainDescAt m ztlkt zta
      (regHost ztgm (Qof P).n
        (BuildNF.buildNF ztwiq zta L E) ztos) C) →
    NFWithin c.nmem ztchk ztm NR → IsNF ztc zta NR →
    c.nreg ALLOC + xKappa * ztxdv ≤ W →
    XE P W (xvOf P c C (BuildNF.buildNF ztwiq zta L E) NR)
        (BuildNF.buildNF ztwiq zta L E) NR
        (rasOf (BuildNF.buildNF ztwiq zta L E) ztos) ztm
        c.nmem ∧
      SetupFacts P W c C (BuildNF.buildNF ztwiq zta L E) NR

/-- **Glue B**: the triples of the kept chord records describe the kept chords. -/
def PostMath : Prop :=
  ∀ (P : Polygon) (li : Bool) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point) (r : ℕ)
    (C : Chain) (NR : NF) (v : XV), XHyp P li L E reg r C NR →
    v.m = C.m → v.T = C.topIdx → v.β = C.sideBeta → v.li = li →
    v.H = regHost li (Qof P).n (BuildNF.buildNF ztwiq zta L E) r →
    {x | ∃ y ∈ xL P v NR NR.chords.length, x = (recOf y).toSet ztwiq zta} =
        Extract.kept ztcz ztxki ∧
      ((xL P v NR NR.chords.length).map
        fun y => (recOf y).toSet ztwiq zta).Nodup ∧
      (∀ y ∈ xL P v NR NR.chords.length,
        (recOf y).Attached ztwiq zta ∧ y.1 < (Qof P).n) ∧
      ∀ q, q < 2 * (xL P v NR NR.chords.length).length →
        ∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
          OnArcKey zta (BuildNF.buildNF ztwiq zta L E) j
            (endPos (xL P v NR NR.chords.length) q)
theorem ga_regHost_nil (li : Bool) (n : ℕ) (N : NF) (r : ℕ) (h : (N.region r).arcs.length = 0) :
    regHost li n N r = [] := by
  unfold regHost DrvR.walkItems
  simp_all

/-- An end on an arc of the region is on one of the arcs of the arc list, by comparisons. -/
theorem ga_onArc {P : Polygon} {li : Bool} {N : NF} {r : ℕ}
    (hli : li = true ↔ Mountain.LeftInside zta) (hdh : DistinctHeights zta)
    (hn : 2 ≤ (Qof P).n)
    (hgood : ∀ j, j < N.arcs.length → GoodPos zta (N.arc j).s ∧ GoodPos zta (N.arc j).e)
    (hras : ∀ t, t < (N.region r).arcs.length → (N.region r).arcs.getD t 0 < N.arcs.length)
    {x : WPos} (hx : GoodPos zta x) {j : ℕ} (hj : j ∈ (N.region r).arcs)
    (ho : OnArcKey zta N j x) :
    ∃ t, t < (N.region r).arcs.length ∧ OnArcP zta li N (rasOf N r t) x := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hj
  have e : rasOf N r t = (N.region r).arcs[t] := by
    unfold rasOf; simp_all
  have hjA := hras t ht
  rw [List.getD_eq_getElem _ _ ht] at hjA
  refine ztkna
  zui
  exact (onArc_iff hli hdh hn hx (hgood _ hjA).1 (hgood _ hjA).2).1 ho
set_option maxHeartbeats 16000000 in
/-- **Glue A.** -/
theorem xeGlue : XEGlue := by
  intro P W c L E C NR hG hWh hb1 hbit hLne hok hperm hsort hdeg hNW hr hHost hHB hCP hCs hCm
    hMDwf hMDa hCDa hNRW hNR hroom
  zucm
  zugmd
  zubp
  zufvw
  zukas
  have hli : decide ztlks = true ↔ Mountain.LeftInside zta := by
    simp_all
  zunh
  have X : XHyp P ztgm L E reg ztos C NR :=
    ⟨hG, hli, hLne, hok, hperm, hsort, ⟨hRC, hCS, hAO, hRO⟩, hr, hCP, hCs, hCm, hNR⟩
  zugqc
  obtain ⟨hgood, hinc, hnext, hfree⟩ := X.arc_facts
  obtain ⟨hras1, -, -⟩ := DownMath.regArcs_facts hQ hok hperm hsort X.hK X.hregs hr
  have hras : ∀ t, t < ((BuildNF.buildNF ztwiq zta L E).region ztos).arcs.length →
      ((BuildNF.buildNF ztwiq zta L E).region ztos).arcs.getD t 0 <
        (BuildNF.buildNF ztwiq zta L E).arcs.length := fun t ht => (hras1 t ht).1
  -- memory
  have hNat := hNW.holds
  have hNRat := hNRW.holds
  obtain ⟨b1, -, b3, b4, b5, -⟩ := Restore.nf_bounds hNW
  obtain ⟨c1, c2, -, -, -, -⟩ := Restore.nf_bounds hNRW
  unfold xKappa at hroom
  have hA0W : ztcga := by_omega
  have hK : ztyyl := hNRat.1
  -- the model descriptor is a chain descriptor
  have hMD0 : c.nmem ztghe = 0 := by
    rcases hMDa.holds with ⟨h0, -⟩ | ⟨-, -, hI⟩
    · zulyi
    · exact absurd hI (Restore.chainModel_ne_interior C _)
  have hCD := hCDa.holds
  obtain ⟨hlen64, hwfP, -, -⟩ := (hMDwf.2 hMD0).2 _ _ hCD
  have hwf : HostWF (Qof P).n (regHost ztgm (Qof P).n
      (BuildNF.buildNF ztwiq zta L E) ztos) := by
    grind
  have hmp : C.m + 1 = ((regHost ztgm (Qof P).n
      (BuildNF.buildNF ztwiq zta L E) ztos).pts (Qof P).n).length := by
    rw [hCm, hCP]; zunoo
  zubb
  have hptsle := Host.pts_length_le hwf
  have hptsle' : (regHost ztgm (Qof P).n
      (BuildNF.buildNF ztwiq zta L E) ztos).length * (Qof P).n ≤
      64 * (Qof P).n := Nat.mul_le_mul_right _ hlen64
  -- the region has an arc
  have hnRA1 : 1 ≤ ((BuildNF.buildNF ztwiq zta L E).region ztos).arcs.length := by
    zuccr
    have hnil := ga_regHost_nil ztgm (Qof P).n
      (BuildNF.buildNF ztwiq zta L E) ztos by_omega
    grind
  have hnRA32 := regHost_length_ge ztgm (Qof P).n
    (BuildNF.buildNF ztwiq zta L E) ztos
  have hr' : c.nreg 217001 < (BuildNF.buildNF ztwiq zta L E).regions.length := hr
  have hreg4 := b4 _ hr
  have hRA := b5 _ hr _ (show ((BuildNF.buildNF ztwiq zta L E).region
    ztos).arcs.length - 1 < _ by omega)
  have hA1 : 1 ≤ (BuildNF.buildNF ztwiq zta L E).arcs.length := by
    have := hras 0 by_omega; omega
  have hAB := b3 _ (show (BuildNF.buildNF ztwiq zta L E).arcs.length - 1 < _ by omega)
  refine ⟨⟨hG, hli, hdh, by_omega, by_omega, rfl, by show _ + 5 * NR.chords.length ≤ W; omega,
    fun mm hmm => hHost mm hmm, hwf, hlen64, hHB, hm1, hmp, C.topIdx_le, ?_, ?_, ?_, rfl,
    fun j hj => hgood j hj, hinc, hnext, hfree, ?_, ?_, fun t ht => hras t ht, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl⟩, ?_⟩
  · -- the chord records of `N_R`
    intro mm hmm i hi
    have h := ((hNRW mm hmm).2.2.2.2.2.1 i hi)
    rw [hmm ztrly by_omega] at h
    exact ztcbv
  · tauto
  · zug
    obtain ⟨A, B, hAB, hc, hh, hadm, hl, hrr, hzl, hzr⟩ := Y.chord_data hi
    have h1 := hl.1
    have h2 := hrr.1
    rw [C.sideWalk_n] at h1 h2
    exact ⟨by_omega, by show _ ≤ 2 * C.m + 6; omega, by show _ ≤ 2 * C.m + 6; omega⟩
  · -- the arc records of `N`
    intro mm hmm j hj
    have h := ((hNW mm hmm).2.2.2.2.2.2.1 j hj)
    rw [hmm ztrlx by_omega] at h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · -- the arc list of the region
    intro mm hmm t ht
    have h := ((hNW mm hmm).2.2.2.2.2.2.2.1 _ hr').2.2.2.1 t ht
    rw [hmm ztlkr by_omega, hmm zthuo by_omega,
      hmm ztccq by_omega] at h
    zubh
  · tauto
  · show ztzdu + ((BuildNF.buildNF ztwiq zta L E).region ztos).arcs.length ≤ c.nreg ALLOC; omega
  · show ((BuildNF.buildNF ztwiq zta L E).region ztos).arcs.length ≤ 32; omega
  · show 2 * (BuildNF.buildNF ztwiq zta L E).arcs.length + 2 ≤ W; omega
  · -- the kept chords
    intro i hi hk
    have hkeep := (Y.kept_iff hi).1 hk
    obtain ⟨-, -, -, hpl, hpr, ⟨j1, hj1, ho1⟩, ⟨j2, hj2, ho2⟩⟩ := Y.kept_pos hi hkeep
    have hgp : ∀ p, ProperPos ztwiq zta (Qof P).n
        (xPos (Qof P).n (regHost ztgm (Qof P).n
          (BuildNF.buildNF ztwiq zta L E) ztos) (decide (c.nreg 217002 = 1))
          C.m C.topIdx C.sideBeta (NR.chord i).h p) →
        GoodPos zta (xPos (Qof P).n (regHost ztgm (Qof P).n
          (BuildNF.buildNF ztwiq zta L E) ztos) (decide (c.nreg 217002 = 1))
          C.m C.topIdx C.sideBeta (NR.chord i).h p) := fun p hp => by
      refine ⟨hp, by simp [xPos], ?_⟩
      show pEdge _ _ _ < _
      refine pEdge_lt _ (hpt_lt hwf by_omega ?_)
      have := tK_le C.sideBeta hm1 (T := C.topIdx) p
      omega
    exact ⟨hgp _ hpl, hgp _ hpr, ga_onArc hli hdh by_omega hgood hras (hgp _ hpl) hj1 ho1,
      ga_onArc hli hdh by_omega hgood hras (hgp _ hpr) hj2 ho2⟩
  · -- the set-up facts
    refine ⟨hCD.2.2.2.1, hCD.2.2.2.2.1, hCD.2.2.2.2.2, (hHost.holds).1, hK, hNat.2.1,
      ((hNat.2.2.2.2.2.2.2.1 _ hr').1), by_omega, by have := hMDwf.1; omega, ?_, by_omega,
      by omega, by_omega, by_omega, by show ztzdu ≤ W; omega, by_omega⟩
    omega
open Set
open BuildNF (buildNF)
section GlueB
variable {P : Polygon} {v : XV} {NR : NF}

/-- Membership in the kept record list. -/
theorem mem_kl {i t : ℕ} : t ∈ kl P v NR i ↔ t < i ∧ kR P v ztqaj := by
  unfold kl; simp

/-- The kept record list has no repetition. -/
theorem kl_nodup (i : ℕ) : (kl P v NR i).Nodup := List.nodup_range.filter _

/-- The chord record `t < #chords` is a member of the record list. -/
theorem chord_mem_chords {t : ℕ} (ht : t < NR.chords.length) : NR.chord t ∈ NR.chords := by
  zuub
end GlueB

/-- **Glue B**: the triples of the kept chord records describe the kept chords. -/
theorem postMath : PostMath := by
  intro P li L E reg r C NR v X hm hT hβ hli hH
  zugqc
  set K := NR.chords.length with hKdef
  -- the values agree with the chain, the bit and the host
  have hxT : ∀ t, xT P v NR t = xTriple (Qof P).n
      (regHost li (Qof P).n (BuildNF.buildNF ztwiq zta L E) r) li C.m C.topIdx
      C.sideBeta (NR.chord t).h (NR.chord t).lp (NR.chord t).rp := by
    intro t; unfold xT; simp_all
  have hkR : ∀ t, t < NR.nChords → (kR P v ztqaj ↔
      ((NR.chord t).toSet ztc zta ∩ reg r).Nonempty) := by
    intro t ht; unfold kR; rw [hm, hT, hβ, hli, hH]; exact Y.kept_iff ht
  -- the facts of a kept record
  have hset : ∀ t ∈ kl P v NR K, (recOf ztgmy).toSet ztwiq zta =
      (NR.chord t).toSet ztc zta := by
    zucj
    zubxq
    rw [hxT]
    exact (Y.kept_pos htK ztgwa).1
  have hatt : ∀ t ∈ kl P v NR K, (recOf ztgmy).Attached ztwiq zta ∧
      (xT P v NR t).1 < (Qof P).n := by
    zucj
    zubxq
    zugvr

    tauto
  have hon : ∀ t ∈ kl P v NR K,
      (∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
        OnArcKey zta (BuildNF.buildNF ztwiq zta L E) j
          (recOf ztgmy).lpos) ∧
      (∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
        OnArcKey zta (BuildNF.buildNF ztwiq zta L E) j
          (recOf ztgmy).rpos) := by
    zucj
    zubxq
    zugvr

    exact ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩
  zudfi
  · -- the kept chords
    zumx
    constructor
    · zuifw
      zumvn
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
      zubxq
      rw [hset t ht]
      exact ⟨⟨NR.chord t, chord_mem_chords htK, rfl⟩, (hkR t htK).1 hk⟩
    · rintro ⟨⟨c, hc, rfl⟩, hne⟩
      obtain ⟨t, htK, rfl⟩ := List.getElem_of_mem hc
      have hct : NR.chord t = NR.chords[t] := by
        zuub
      have ht : t ∈ kl P v NR K := mem_kl.2 ⟨htK, (hkR t htK).2 by_simp_all⟩
      refine ⟨xT P v NR t, List.mem_map.2 ztbik, ?_⟩
      grind
  · -- no repetition
    have e : (xL P v NR K).map (fun y => (recOf y).toSet ztwiq zta) =
        (kl P v NR K).map (fun t => (NR.chord t).toSet ztc zta) := by
      unfold xL
      simp_all
    zui
    exact (kl_nodup K).map_on fun t ht t' ht' h =>
      X.hNR.2.1 t t' (mem_kl.1 ht).1 (mem_kl.1 ht').1 h
  · -- attached, in range
    zusy
    zumvn
    grind
  · -- the ends on arcs of the region
    zuco
    have hlen : (xL P v NR K).length = (kl P v NR K).length := by
      unfold xL; simp
    have hq2 : q / 2 < (kl P v NR K).length := by_omega
    have ht : ztqsn[q / 2] ∈ kl P v NR K := List.getElem_mem hq2
    have hget : (xL P v NR K).getD ztbeu ztt = xT P v NR (ztqsn[q / 2]) := by
      unfold xL
      grind
    zuiqc
    grind
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE keyBkt endPos)
@[expose] public section
def setupB : Stmt :=
  block [.inputSize 217020, .constN 217027 1, .constN 217041 6, .constN 217044 2,
    .copyN 217026 217002,
    .constN 217106 3, .constN 217107 4, .constN 217108 5, .constN 217109 7,
    .addN 217100 217005 217106, .loadN 217021 217100,
    .addN 217100 217005 217107, .loadN 217023 217100,
    .addN 217100 217005 217108, .loadN 217024 217100,
    .addN 217022 217021 217021, .addN 217042 217022 217041,
    .loadN 217034 217003, .addN 217035 217003 217027,
    .loadN 217028 217006, .addN 217100 217006 217106, .loadN 217029 217100,
    .addN 217100 217000 217027, .loadN 217030 217100,
    .addN 217100 217000 217107, .loadN 217031 217100,
    .addN 217100 217000 217108, .loadN 217101 217100,
    .addN 217100 217000 217109, .loadN 217103 217100,
    .addN 217104 217001 217001, .addN 217104 217104 217104, .addN 217104 217104 217001,
    .addN 217104 217101 217104, .loadN 217032 217104,
    .addN 217104 217104 217027, .loadN 217105 217104,
    .addN 217033 217103 217105,
    .copyN 217036 9999, .addN 217047 217028 217028, .addN 217047 217047 217028,
    .addN 217037 217036 217047, .addN 217047 217047 217028, .addN 217047 217047 217028,
    .addN 9999 9999 217047,
    .copyN 217045 217036, .copyN 217046 217037, .constN 217038 0, .constN 217039 0,
    .copyN 217040 217029, .constN 217043 0]

/-- **The set-up**: the globals, the allocation of `5 K` words (`K` chords of `N_R`), the
tour offset `tS`. -/
def setupS : Stmt :=
  .seq setupB
    (.ifLtN 217024 217027 zthec
      (.ifLtN 217027 217024 zthec ztoyy))

/-- **Padding**: `3 · 5 K + 2` steps, so that the allocation is paid for. -/
def padS : Stmt := .whileLtN 217043 217047 ztnsc

/-- The outputs. -/
def finS : Stmt := block [.copyN 217010 217036, .copyN 217011 217038, .copyN 217012 217037]

/-- **The extraction (D6).** -/
def xS : Stmt := seqs [setupS, padS, loopS, finS]

/-- The registers the extraction writes. -/
def Bx (r : ℕ) : Bool := decide (ztnfu ∨ r = 9999)

/-- The real registers the extraction writes. -/
def BxR (r : ℕ) : Bool := decide ztnfu
theorem wrM_x : wrM Bx xS = true := by_decide
theorem wrM2_x : wrM2 Bx BxR xS = true := by_decide
section setup
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
/-- **The set-up.** -/
theorem setupS_exec (d : Config) (hw : WordsBounded W d)
    {MD HB BN BR r v2 m T b5 HL K CB A AB RB LB nRA off : ℕ}
    (h00 : d.nreg 217000 = BN) (h01 : d.nreg 217001 = r) (h02 : d.nreg 217002 = v2)
    (h03 : d.nreg 217003 = HB) (h05 : d.nreg 217005 = MD) (h06 : d.nreg 217006 = BR)
    (mMD3 : d.nmem ztua = m) (mMD4 : d.nmem (MD + 4) = T) (mMD5 : d.nmem ztnmy = b5)
    (mHB : d.nmem HB = HL) (mBR : d.nmem BR = K) (mBR3 : d.nmem (BR + 3) = CB)
    (mBN1 : d.nmem (BN + 1) = A) (mBN4 : d.nmem (BN + 4) = AB) (mBN5 : d.nmem (BN + 5) = RB)
    (mBN7 : d.nmem (BN + 7) = LB) (mR0 : d.nmem ztqch = nRA)
    (mR1 : d.nmem ztenw = off)
    (hnW : P.n ≤ W) (hMD : MD + 5 ≤ W) (hm : 2 * m + 6 ≤ W) (hHB : HB + 1 ≤ W) (hBR : BR + 3 ≤ W)
    (hBN : BN + 7 ≤ W) (hR : RB + 5 * r + 1 ≤ W) (hLB : LB + off ≤ W)
    (hA : d.nreg ALLOC + 5 * K ≤ W) (hW7 : 7 ≤ W) :
    ∃ d' k, Exec P W setupS d d' k ∧ k ≤ 60 ∧
      d'.nreg 217020 = P.n ∧ d'.nreg 217021 = m ∧ d'.nreg 217022 = 2 * m ∧
      d'.nreg 217025 = (if b5 = 1 then T else 2 * m - T) ∧ d'.nreg 217026 = v2 ∧
      d'.nreg 217027 = 1 ∧ d'.nreg 217028 = K ∧ d'.nreg 217030 = A ∧ d'.nreg 217031 = AB ∧
      d'.nreg 217032 = nRA ∧ d'.nreg 217033 = LB + off ∧ d'.nreg 217034 = HL ∧
      d'.nreg 217035 = HB + 1 ∧ d'.nreg 217036 = d.nreg ALLOC ∧
      d'.nreg 217037 = d.nreg ALLOC + 3 * K ∧ d'.nreg 217041 = 6 ∧
      d'.nreg 217042 = 2 * m + 6 ∧ d'.nreg 217044 = 2 ∧ d'.nreg 217038 = 0 ∧
      d'.nreg 217039 = 0 ∧ d'.nreg 217040 = CB ∧ d'.nreg 217043 = 0 ∧
      d'.nreg 217045 = d.nreg ALLOC ∧ d'.nreg 217046 = d.nreg ALLOC + 3 * K ∧
      d'.nreg 217047 = 5 * K ∧ d'.nreg ALLOC = d.nreg ALLOC + 5 * K ∧ d'.nmem = d.nmem := by
  zuhp
  zvnek at hA ⊢
  have mR0' : d.nmem (RB + ztkde) = nRA := by
    grind
  have mR1' : d.nmem (RB + ztkde + 1) = off := by
    grind
  obtain ⟨d1, k1, e1, hk1, a20, a21, a22, a23, a24, a26, a27, a28, a30, a31, a32, a33, a34, a35,
      a36, a37, a41, a42, a44, a38, a39, a40, a43, a45, a46, a47, a99, m1⟩ :
      ∃ d1 k1, Exec P W setupB d d1 k1 ∧ k1 ≤ 51 ∧
      d1.nreg 217020 = P.n ∧ d1.nreg 217021 = m ∧ d1.nreg 217022 = 2 * m ∧
      d1.nreg 217023 = T ∧ d1.nreg 217024 = b5 ∧ d1.nreg 217026 = v2 ∧
      d1.nreg 217027 = 1 ∧ d1.nreg 217028 = K ∧ d1.nreg 217030 = A ∧ d1.nreg 217031 = AB ∧
      d1.nreg 217032 = nRA ∧ d1.nreg 217033 = LB + off ∧ d1.nreg 217034 = HL ∧
      d1.nreg 217035 = HB + 1 ∧ d1.nreg 217036 = d.nreg 9999 ∧
      d1.nreg 217037 = d.nreg 9999 + 3 * K ∧ d1.nreg 217041 = 6 ∧
      d1.nreg 217042 = 2 * m + 6 ∧ d1.nreg 217044 = 2 ∧ d1.nreg 217038 = 0 ∧
      d1.nreg 217039 = 0 ∧ d1.nreg 217040 = CB ∧ d1.nreg 217043 = 0 ∧
      d1.nreg 217045 = d.nreg 9999 ∧ d1.nreg 217046 = d.nreg 9999 + 3 * K ∧
      d1.nreg 217047 = 5 * K ∧ d1.nreg 9999 = d.nreg 9999 + 5 * K ∧ d1.nmem = d.nmem := by
    unfold setupB
    exec_block
    all_goals (try (config_simp; simp (config := { failIfUnchanged := false }) only [h00, h01, h02,
      h03, h05, h06, mMD3, mMD4, mMD5, mHB, mBR, mBR3, mBN1, mBN4, mBN5, mBN7, mR0', mR1']; omega))
    all_goals (try (refine ⟨by omega, ?_⟩))
    all_goals (repeat' apply And.intro)
    all_goals (config_simp <;> simp (config := { failIfUnchanged := false }) only [h00, h01, h02,
      h03, h05, h06, mMD3, mMD4, mMD5, mHB, mBR, mBR3, mBN1, mBN4, mBN5, mBN7, mR0', mR1'])
    all_goals omega
  zuqj
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (a := 217024) (b := 217027)
    (r := 217025) (t := block [.subN 217025 217022 217023])
    (e := .ifLtN 217027 217024 zthec ztoyy)
    (d := d1) (K := 3) (fun _ => x_mono (x_sub d1 hw1 217025 217022 217023) by_omega)
    (fun _ => x_ifR (fun _ => x_sub d1 hw1 217025 217022 217023)
      (fun _ => x_copy d1 hw1 217025 217023))
  have o : ∀ r, r ≠ 217025 → d2.nreg r = d1.nreg r := fun r hr => n2.other hr
  refine ⟨d2, k1 + k2, .seq e1 e2, by_omega, by_grind,
    by grind, by_grind, ?_,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind, by zuojp⟩
  rw [n2.same, a24, a27, a22, a23]
  grind
end setup
section pad
variable {P : Polygon} {W : ℕ}

/-- **Padding**: exactly `3 (N - j) + 2` steps. -/
theorem padS_exec (d : Config) (hw : WordsBounded W d) {N j : ℕ} (h43 : d.nreg 217043 = j)
    (h47 : d.nreg 217047 = N) (h27 : d.nreg 217027 = 1) (hj : j ≤ N) (hNW : N ≤ W) :
    ∃ d' k, Exec P W padS d d' k ∧ k = 3 * zthbl + 2 ∧ NRegs d d' (upd d.nreg 217043 N) := by
  induction hn : N - j generalizing d j with
  | zero =>
    zubaq

    refine ⟨d, 2, .whileLtN_false by_omega hw, by_omega, ?_⟩
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    rw [← h43, Machine.upd_eq_self]
  | succ t ih =>
    zufvj
    have hb : d.nreg 217043 + d.nreg 217027 ≤ W := by_omega
    have ea := Machine.Exec.addN (P := P) hw 217043 217043 217027 hb
    have e1 : Exec P W ztnsc d
        { d with nreg := upd d.nreg 217043 (d.nreg 217043 + d.nreg 217027) } (0 + 1) :=
      Exec.block_cons ea (Exec.block_nil ea.wb_right)
    have b43 : ({ d with nreg := upd d.nreg 217043 (d.nreg 217043 + d.nreg 217027) } : Config).nreg
        217043 = j + 1 := by simp [h43, h27]
    obtain ⟨d', k', e', hk', n'⟩ := ih _ e1.wb_right b43 by_tauto by_tauto by_omega
      by_omega
    refine ⟨d', 0 + 1 + 2 + k', .whileLtN_true by_omega e1 e', by_omega, ?_⟩
    obtain ⟨n1, n2, n3, n4, n5⟩ := n'
    refine ⟨?_, n2, n3, n4, n5⟩
    rw [n1]; simp
end pad
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (regHost keyBkt OnArcKey endPos)
@[expose] public section
theorem keyBkt_congr {Q : Polygon} {N N' : NF} (ha : N.arcs = N'.arcs) (x : WPos) :
    keyBkt Q N x = keyBkt Q N' x := by
  zuded
  obtain ⟨c', a', g', s', d', o', l'⟩ := N'
  simp only at ha
  subst ha
  rfl
theorem liV_decide {x : ℕ} (hx : x ≤ 1) : liV (decide (x = 1)) = x := by
  unfold liV; grind
set_option maxHeartbeats 8000000 in
/-- **The extraction meets its contract**, given the two pieces of glue. -/
theorem extractRamSpec_of (hA : XEGlue) (hB : PostMath) : DrvR.ExtractRamSpec := by
  refine ⟨xS, xKappa, ?_⟩
  zubgq
  obtain ⟨hG, hW, h02, hli2, L, E, C, NR, hLne, hL, hperm, hsort, hdeg, hNw, hr, hHost, hHBA, -,
    hCP, hCs, hCm, hMDwf, hMD, hCD, hNRw, hNR⟩ := hpre
  obtain ⟨XEh, SF⟩ := hA P W c L E C NR hG hW h02 hli2 hLne hL hperm hsort hdeg hNw hr hHost hHBA
    hCP hCs hCm hMDwf hMD hCD hNRw hNR hroom
  obtain ⟨sM3, sM4, sM5, sHB, sBR, sBN1, sR0, sPn, sMD, sm, sHB1, sBR3, sBN7, sR1, sRA, s7⟩ := SF
  set N := BuildNF.buildNF ztwiq zta L E with hNdef
  set v := xvOf P c C N NR with hvdef
  have hK : v.K = NR.chords.length := rfl
  have hA0 := XEh.hA0
  -- set-up
  obtain ⟨d1, k1, e1, hk1, a20, a21, a22, a25, a26, a27, a28, a30, a31, a32, a33, a34, a35, a36,
      a37, a41, a42, a44, a38, a39, a40, a43, a45, a46, a47, a99, m1⟩ :=
    setupS_exec (P := P) c hw (h00 := rfl) (h01 := rfl) (h02 := rfl) (h03 := rfl) (h05 := rfl)
      (h06 := rfl) sM3 sM4 rfl sHB sBR rfl sBN1 rfl rfl rfl sR0 rfl sPn sMD sm sHB1 sBR3 sBN7 sR1
      sRA hA0 s7
  zuqj
  zudzj
  have g1 : ztumo := by
    refine ⟨by_omega, a21, a22, ?_, by rw [a26]; exact (liV_decide h02).symm, a27, a28,
      a30, a31, a32, a33, a34, a35, a36, a37, a41, a42, a44⟩
    rw [a25]
    show _ = tS C.m C.topIdx C.sideBeta
    unfold tS
    grind
  -- padding
  obtain ⟨d2, k2, e2, hk2, n2⟩ := padS_exec (P := P) d1 hw1 a43 a47 a27 ztbg
    by_omega
  have o2 : ∀ r, r ≠ 217043 → d2.nreg r = d1.nreg r := fun r hr => n2.other hr
  zump
  have g2 : ztump := g1.congr fun r hr => o2 r (by
    rintro rfl; revert hr; decide)
  have m2 : d2.nmem = c.nmem := by zuojp
  -- the loop
  obtain ⟨d3, k3, e3, hk3, g3, c38, cm, cl, cb, f3⟩ := loopS_exec XEh d2 hw2
    (fun a _ => by rw [m2]) g2 ((o2 217039 by_decide).trans a39)
    ((o2 217040 by_decide).trans a40) ((o2 217038 by_decide).trans a38)
    ((o2 217045 by_decide).trans a45) ((o2 217046 by_decide).trans a46)
  zubgh
  -- the outputs
  obtain ⟨d4, k4, e4, hk4, b10, b11, b12, g4, m4⟩ : ∃ d4 k4, Exec P W finS d3 d4 k4 ∧ k4 ≤ 3 ∧
      d4.nreg 217010 = d3.nreg 217036 ∧ d4.nreg 217011 = d3.nreg 217038 ∧
      d4.nreg 217012 = d3.nreg 217037 ∧
      (∀ r, r ≠ 217010 → r ≠ 217011 → r ≠ 217012 → d4.nreg r = d3.nreg r) ∧
      d4.nmem = d3.nmem := by
    unfold finS
    exec_block
    refine ⟨by_omega, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩ <;> config_simp
    simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h3]
  have ex : Exec P W xS c d4 (k1 + ztbqj) := by
    simp only [xS, seqs_cons₂, seqs_one]
    exact .seq e1 ztbal
  have fm := exec_frameM ex wrM_x
  have fr := exec_frameM2 ex wrM2_x
  -- the allocator
  have hal : d4.nreg ALLOC = c.nreg ALLOC + 5 * NR.chords.length := by
    show d4.nreg 9999 = _
    rw [g4 9999 by_decide by_decide by_decide, f3.1 9999 by_decide, o2 9999 by_decide]
    exact a99
  have hlen := xL_length_le P v NR v.K
  have hKc : ztyyl := sBR
  refine ⟨d4, k1 + ztbqj, ex, ?_, ⟨fun q hq1 hq2 => ?_, ?_⟩, ?_⟩
  · -- cost
    show _ ≤ xKappa * ztxdv
    rw [hKc]; unfold xKappa
    omega
  · -- registers of the band outside the reserved range
    refine fm.1 q ?_
    zuoed
    have : q / 10000 = 21 := hq1
    omega
  · -- the outputs
    intro L' E' C' NR' reg' hLne' hL' hperm' hsort' hNat' hregs' hCP' hCs' hCm' hNRat' hNR'
    obtain ⟨rc, ra, rr⟩ := DrvH.nfAt_recs hNw.nfAt hNat'
    have hreg : regHost ztgm (Qof P).n N ztos =
        regHost ztgm (Qof P).n
          ztbapb ztos :=
      DrvH.regHost_congr rc ra rr _ _ _
    have hP : ztmsw := by_grind
    have hCC : ztkzv := by
      have hs : ztidk := by_omega
      have hm : C'.m = C.m := by_grind
      cases C; cases C'
      grind
    subst hCC
    obtain ⟨rcR, -, -⟩ := DrvH.nfAt_recs hNRw.nfAt hNRat'
    have hchR : ∀ t, NR'.chord t = NR.chord t := fun t => by simp only [NF.chord, rcR]
    have hxL : xL P v NR' NR'.chords.length = xL P v NR v.K := by
      show _ = xL P v NR NR.chords.length
      unfold xL kl xT
      rw [← rcR]
      simp only [hchR]
    have X' : XHyp P ztgm L' E' reg' ztos C' NR' :=
      ⟨hG, by_grind, hLne', hL', hperm', hsort', hregs',
        by have := hr; simp only [NF.nRegions] at this ⊢; grind, hCP', hCs',
        hCm', hNR'⟩
    obtain ⟨pS, pN, pA, pO⟩ := hB P ztgm L' E' reg' ztos C'
      NR' v X' rfl rfl rfl rfl hreg
    rw [hxL] at pS pN pA pO
    have e10 : d4.nreg 217010 = c.nreg ALLOC := b10.trans g3.r36
    have e12 : d4.nreg 217012 = c.nreg ALLOC + 3 * NR.chords.length := b12.trans g3.r37
    refine ⟨xL P v NR v.K, by_omega, by_omega, by_omega, by_omega, by_omega,
      by rw [m4, e10]; exact cl, pS, pN, pA,
      fun q hq => ⟨?_, pO q hq⟩⟩
    rw [m4, e12, ← keyBkt_congr ra]
    exact cb q hq
  · -- the frame
    refine ⟨fun r hr hra => fm.1 r ?_, fun r hr => fr r ?_, fun a ha => ?_, fun a _ => ?_,
      fm.2.2.2, ?_, ?_⟩
    · have h21 : ztmwm := fun h => hr (by
        show r / 10000 ∈ ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ)
        zvmwc; decide)
      have h99 : zteif := hra
      zuoed; omega
    · have h21 : ztmwm := fun h => hr (by
        show r / 10000 ∈ ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ)
        zvmwc; decide)
      simp only [BxR, decide_eq_false_iff_not]; omega
    · grind
    · rw [fm.2.2.1]
    · omega
    grind
theorem extractRamSpec : DrvR.ExtractRamSpec := extractRamSpec_of xeGlue postMath
end
end DrvX
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {R : ℕ} {c : Config} {r : ℕ}
/-- A well-formed model descriptor of a chain model below `E` survives a change of the memory at
or above `E` (and a larger bound). -/
theorem modelDesc_keep {m m' : ℕ → ℕ} {D E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ModelDescWF P E m D) (h0 : m D = 0) (hC : ChainDescAt m ztef zta H C)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescWF P E' m' D ∧ m' D = 0 ∧ ChainDescAt m' ztef zta H C := by
  obtain ⟨hD6, hch⟩ := hwf
  have hcw := hch h0
  zubks
  have hc : ∀ j, j < 5 → m' _ = m ztjht := fun j hj => he _ by_omega
  zudye
  have h0' : m' D = 0 := by_grind
  refine ⟨⟨by_omega, fun _ => chainWF_copy hcw hC he hc by_omega hE⟩, h0', hC'⟩

/-! ## The shooting context -/

/-- **The shooting context** at `R`: the facts the shots need, for the chain `C` on the host `H`. -/
def ShotCtx (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ)
    (c : Config) (H : Host) (C : Chain) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztbwu ztm ∧
    c.nreg ztbmf ≤ X.cap P c.nmem ztbwu ∧
    ModelDescWF P ztm c.nmem ztdct ∧ c.nmem ztdct = 0 ∧
    ChainDescAt c.nmem ztfqj zta H C ∧ c.nreg ztvh = c.nreg R + 1 ∧
    ztxpd ∧
    Ok P ztc ∧ 2 * C.m + 7 ≤ W ∧ c.nreg ztgx = 0 ∧ c.nreg zthl = 1 ∧
    BitIs c ztbgt ztwyb
theorem ShotCtx.modelDesc
 {H : Host} {C : Chain} (h : ShotCtx P W X Ok R c H C) :
    ModelDescAt c.nmem ztdct zta ztc :=
  Or.inl ⟨h.2.2.2.2.2.1, H, C, h.2.2.2.2.2.2.1, rfl⟩
theorem ShotCtx.chainWF
 {H : Host} {C : Chain} (h : ShotCtx P W X Ok R c H C) :
    ChainWF P ztm c.nmem ztwup := by
  rw [h.2.2.2.2.2.2.2.1]; exact h.2.2.2.2.1.2 h.2.2.2.2.2.1

/-- **The shooting context survives** a frame of the oracle bands that keeps the registers
`R … R + 8` and `R + 30 … R + 35`. -/
theorem ShotCtx.frame
    (hXl : X.CapLocal) {R : ℕ} {c c' : Config} {H : Host} {C : Chain} {Wr : ℕ → Prop} {k : ℕ}
    (h : ShotCtx P W X Ok R c H C) (hf : FrameR oracleBands Wr c c' k)
    (hr : ∀ i, ztikz → c'.nreg ztly = c.nreg ztly) :
    ShotCtx P W X Ok R c' H C := by
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσ⟩ := h
  zuddv
  have he := hmem
  have r0 : ztmuk := by simpa using hr 0 by_omega
  obtain ⟨mw', h0', hC'⟩ := modelDesc_keep hmwf h0 hC he hA
  obtain ⟨-, -, hEb, -⟩ := (hmwf.2 h0).2 H C hC
  refine ⟨hG, hHW, ?_, ?_, by_simp_all, by_simp_all, by_simp_all,
    by simp_all, ?_, hOk, hm, by_simp_all,
    by simp_all, ⟨by rw [hr 35 by_omega]; exact hσ.1,
      by rw [hr 35 by_omega, hr 6 by_omega]; exact hσ.2⟩⟩
  · rw [hr 8 by_omega]
    exact X.mono P _ _ _ _ hA (X.local_ P _ _ _ _ by_simp_all hX)
  · rw [hr 8 by_omega, hr 7 by_omega, hXl P c.nmem c'.nmem _ _ he hX]; omega
  · zujap
    rw [r0] at hH'
    have hb : c'.nmem _ = c.nmem ztfqj := he _ (by
      have := hmwf.1; omega)
    rw [hb] at hH'
    have hH : HostAt c'.nmem _ H := hostAt_agree hC.1 hEb he
    zugcg
    exact hreg H hC.1

/-! ## Bands -/
theorem rd_shoot (c : Config) (i : ℕ) : rd c bShoot i = c.nreg ztsrd := by
  rfl

/-- The caller's registers are outside the oracle bands. -/
theorem band_R (hR : RegsOK R) {i : ℕ} (hi : i < 300) : bandOf ztly ∉ oracleBands := by
  zuhaf
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, bandOf]
  omega
theorem band_prim (h : Bprim r = true) : bandOf r ∈ oracleBands := by
  have := (Bprim_band r h).1
  simp only [primBands, oracleBands, kernelBands, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at this ⊢
  tauto
theorem band_locate (h : 50000 ≤ r ∧ r < 60000) : bandOf r ∈ oracleBands := by
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, bandOf]
  omega
theorem band_shoot (h : 140000 ≤ r ∧ r < 150000) : bandOf r ∈ oracleBands := by
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, bandOf]
  omega

/-! ## The leaf with the shooter -/

/-- The registers of the caller's block written by a leaf. -/
def WrLeaf (R : ℕ) (r : ℕ) : Prop := ztbeb ∨ ztent

/-- **One shot at the piece of level `3`**: the running minimum extends to the piece. -/
theorem leaf_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) {H : Host} {C : Chain} (hctx : ShotCtx P W X Ok R c H C)
    (hp1 : ProperPos ztc zta P.n (pieceR c ztmp).1)
    (hp2 : ProperPos ztc zta P.n (pieceR c ztmp).2)
    (he1 : (pieceR c ztmp).1.edge < (chainModel C).W.n)
    (he2 : (pieceR c ztmp).2.edge < (chainModel C).W.n)
    (hi1 : (pieceR c ztmp).1.hgt = 0 ∨
      (chainModel C).InnerPt ((chainModel C).pos zta (pieceR c ztmp).1))
    (hi2 : (pieceR c ztmp).2.hgt = 0 ∨
      (chainModel C).InnerPt ((chainModel C).pos zta (pieceR c ztmp).2))
    (hwt : (chainModel C).arcWt ztwxo
      ztwxp ≤ c.nreg ztbmf)
    {o : Origin} (ho : OriginIn c ztbza o) (hol : o.Lt P.n ztc)
    (hof : ztbnw ∨ ((chainModel C).InnerPt ztwqq ∧
      ∀ x, o = .walk x → ProperPos ztc zta P.n x))
    (hon : o.eval ztc zta ∉ (chainModel C).arcSet
      ztwxo
      ztwxp)
    (hoy : |(o.eval ztc zta).2| < C.radius) {S : Set Point}
    (hbest : BestOK P C R c S ztwqq ztwkv)
    (hroom : c.nreg ALLOC + F ztkx + 17500 ≤ W) :
    ∃ c' k, Exec P W (leaf sh R) c c' k ∧ k ≤ F ztkx + 17500 ∧
      BestOK P C R c' (S ∪ (chainModel C).arcSet
        ztwxo
        ztwxp)
        ztwqq ztwkv ∧
      FrameR oracleBands ztmcm c c' k := by
  zubwa
  zubio
  zurm

  -- the shooter's inputs

  simp only [setList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  zubuc
  have k1 := fun r hr =>
    f₁.1 r ztnuz
  zucao

  have hMD := hctx.modelDesc
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ := hctx
  have hO1 : ztyyi := by
    zudss
    · exact s5
    · exact s6
    omega
  have hpc : pieceR c₁ 140001 = pieceR c ztmp := by
    simp only [pieceR, posR, Prod.mk.injEq, WPos.mk.injEq]
    grind
  -- the shot
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, fr₂⟩ := hsh P W c₁ e₁.wb_right
    ⟨hG, hHW, by zuntt; exact hX,
      by zunnb; omega,
      by zuntu; omega,
      fun _ H' C' hC' => by
        rw [rd_shoot, s0, hM1] at hC'
        zunht; exact hreg H' hC'.1, M,
      by rw [rd_shoot, s0, hM1]; omega, hOk,
      by zunah; exact hp1, by zunai; exact hp2,
      by zuoob; exact he1, by zuooc; exact he2,
      by zunah; exact hi1, by zunai; exact hi2,
      by zunch; exact hwt,
      o, hol, hO1, hof, by zuneq; exact hon⟩
    ztezq
  replace hk₂ : k₂ ≤ F ztkx := by
    zudhc

  zubbp

  -- registers of the caller's block survive the shot
  have hR2 : ztkog := fun i hi => by
    rw [fr₂.1 _ (fun hb => band_R hR hi ztvsp) ztu, hR1 i hi]
  have F01 : FrameR oracleBands ztmcm c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
    right; simp [setList] at hr; exact band_shoot by_omega) by_rfl _
  have F12 : FrameR oracleBands ztmcm c₁ c₂ k₂ :=
    (FrameR.of_frame fr₂).mono hBs ztb le_rfl
  zulgy
  have ctx₂ :=
    ShotCtx.frame hXl ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ F02
      ztnyx
  have best₂ := hbest.congr zttmt zttmu
    zttmv (hR2 24 by_omega) (hR2 25 by_omega) (hR2 26 by_omega)
    (hR2 27 by_omega)
  zue
  zuefy
  have hA2 : ztyui := by
    have := F12.2.2.2.2.2.2; omega
  -- no hit
  have nohit : c₂.nreg 140010 ≠ 1 → BestOK P C R c₂ _ z σ := fun hne => by
    zucru

  zuhsd
  · refine ⟨c₂, _, .seq e₁ ztyog, by_omega,
      nohit by_omega, ?_⟩
    exact ztrji
  zuhsf
  · refine ⟨c₂, _, .seq e₁ ztxuf, by_omega,
      nohit by_omega, ?_⟩
    exact ztrji
  -- a hit
  zucmd

  obtain ⟨-, hHW2, -, -, hmwf2, h02, hC2, h342, hreg2, -, -, h302, h312, hσb2⟩ := ctx₂
  obtain ⟨c₃, k₃, e₃, hk₃, best₃, f₃⟩ := leafHit_exec (P := P) hR c₂ w₂ hG hHW2
    (H := H) (C := C) (by zupbr; exact hmwf2.2 h02) by_grind
    (by zupbr; omega) htA hpe hpp hpos hoy h302 h312 hσb2
    ztntn best₂ by_omega
  refine ztedq
  have F23 : FrameR oracleBands ztmcm c₂ c₃ k₃ := FrameR.of_frameB f₃ (fun r hr => by
    simp only [Bhit, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with ((h' | h') | h') | h'
    · exact Or.inl zthrp
    · exact Or.inl (Or.inr h')
    · exact Or.inr (band_prim h')
    · exact Or.inr ztves)
    (by unfold ALLOC; simp only [Bhit, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega) _
  exact (F02.trans F23).mono le_rfl by_grind by_omega
end
end ShotList
end Chazelle.Core
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
@[expose] public section
def copy2List (R ℓ : ℕ) : List ztw := [(rL R ℓ + 10, rL R ℓ + 4), (rL R ℓ + 11, rL R ℓ + 5),
  (rL R ℓ + 12, rL R ℓ + 6), (rL R ℓ + 13, rL R ℓ + 7)]

/-- **The cutting recursion**: `f` levels from level `ℓ`. -/
def levF (sh : Stmt) (R : ℕ) : ℕ → ℕ → Stmt
  | 0, _ => leaf sh R
  | f + 1, ℓ => .seq ztnxh (.ifLtN ztgx ztsj
      (.seq ztxxo (.ifLtN zthl ztsj
        (.seq ztzdm ztxxo) .skip)) .skip)

/-! ## The pieces -/

/-- The points of a list of pieces. -/
def pcSet (M : Model) (Q : Polygon) (L : List ztqx) : Set Point :=
  ⋃ p ∈ L, M.arcSet ztszu ztszv
variable (M : Model) (Q : Polygon)
theorem pcSet_nil : pcSet M Q [] = ∅ := by zupbq
theorem pcSet_single (p : WPos × WPos) :
    pcSet M Q [p] = M.arcSet ztszu ztszv := by zupbq
theorem pcSet_append (L L' : List ztqx) :
    pcSet M Q ztrjv = pcSet M Q L ∪ pcSet M Q L' := by
  ext x; simp [pcSet, or_and_right, exists_or]

/-- **The pieces reached by the recursion** from level `ℓ` (`f` levels), with the holes read in
the registers of `c`. -/
noncomputable def levLeaves (M : Model) (Q : Polygon) (c : Config) (R : ℕ) :
    ℕ → ℕ → WPos × WPos → List ztqx
  | 0, _, q => [q]
  | f + 1, ℓ, q => (levPieces M Q ztwrw q.1 q.2
      ztxwe ztxwf).flatMap (levLeaves M Q c R f (ℓ + 1))

/-- `levLeaves` reads only the hole registers and the level constants. -/
theorem levLeaves_congr (M : Model) (Q : Polygon) {c c' : Config} {R : ℕ}
    (h : ∀ i, ztbje ∨ ztbjd → c'.nreg ztly = c.nreg ztly) :
    ∀ f ℓ, f + ℓ ≤ 3 → ∀ q, levLeaves M Q c' R f ℓ q = levLeaves M Q c R f ℓ q
  | 0, _, _, _ => rfl
  | f + 1, ℓ, hf, q => by
    simp only [levLeaves]
    have e1 : c'.nreg ztkt = c.nreg ztkt := by
      rw [show R + 30 + ℓ = R + (30 + ℓ) by omega]; exact h _ by_omega
    have e2 : c'.nreg _ = c.nreg _ := h 9 by_omega
    have e3 : c'.nreg ztqv = c.nreg ztqv :=
      by rw [show R + 10 + 2 * ℓ = R + (10 + 2 * ℓ) by omega]; exact h _ by_omega
    have e4 : c'.nreg ztqw = c.nreg ztqw :=
      by rw [show R + 11 + 2 * ℓ = R + (11 + 2 * ℓ) by omega]; exact h _ by_omega
    simp only [e1, e2, e3, e4]
    zucr
    funext p
    exact levLeaves_congr M Q h f _ by_omega p

/-! ## Pieces with good ends -/

/-- **A piece with good ends**: normalised, in range, and each a vertex or an inner point. -/
def PieceOK (M : Model) (Q : Polygon) (n : ℕ) (p : WPos × WPos) : Prop :=
  NormPos M Q n p.1 ∧ NormPos M Q n p.2 ∧ p.1.edge < M.W.n ∧ p.2.edge < M.W.n ∧
    (p.1.hgt = 0 ∨ M.InnerPt (M.pos Q p.1)) ∧ (p.2.hgt = 0 ∨ M.InnerPt (M.pos Q p.2))

/-- The ends of a piece of `levPieces` are ends of the arc or hole vertices. -/
theorem levPieces_ends {M : Model} {Q : Polygon} {hp : Prop} [Decidable hp] {a b : WPos}
    {x y : ℕ} {p : WPos × WPos} (h : p ∈ levPieces M Q hp a b x y) :
    (p.1 = a ∨ p.1 = b ∨ p.1 = ztbrb ∨ p.1 = ztcpb) ∧
      (p.2 = a ∨ p.2 = b ∨ p.2 = ztbrb ∨ p.2 = ztcpb) := by
  unfold levPieces at h
  zulsn
  · zuebk
    rcases cut1_cases _ a b ztbrb ztcpb h with
      ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ |
      ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, -, -, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl⟩ <;> simp
  simp_all

/-- **Good ends are preserved by cutting.** -/
theorem pieceOK_levPieces {M : Model} {Q : Polygon} {n : ℕ} {hp : Prop} [Decidable hp]
    {a b : WPos} {x y : ℕ} (hab : PieceOK M Q n ztvk) (hx : x < M.W.n) (hy : y < M.W.n)
    {p : WPos × WPos} (h : p ∈ levPieces M Q hp a b x y) : PieceOK M Q n p := by
  obtain ⟨na, nb, ea, eb, ia, ib⟩ := hab
  have good : ∀ u : WPos, (u = a ∨ u = b ∨ u = ztbrb ∨ u = ztcpb) →
      NormPos M Q n u ∧ u.edge < M.W.n ∧ (u.hgt = 0 ∨ M.InnerPt (M.pos Q u)) := by
    rintro u (rfl | rfl | rfl | rfl)
    · simp_all
    · simp_all
    · exact ⟨normPos_vtx M Q n x, hx, Or.inl rfl⟩
    · exact ⟨normPos_vtx M Q n y, hy, Or.inl rfl⟩
  obtain ⟨h1, h2⟩ := levPieces_ends h
  obtain ⟨g1, g1e, g1i⟩ := good _ h1
  obtain ⟨g2, g2e, g2i⟩ := good _ h2
  trivial

/-! ## The recursion on the RAM -/

/-- The registers of the caller's block written from level `ℓ` on. -/
def WrLev (R ℓ : ℕ) (r : ℕ) : Prop := ztbeb ∨ (rL R ℓ + 4 ≤ r ∧ r < R + 300)

/-- The cost of `f` levels. -/
def levCost (Fg f : ℕ) : ℕ := ztzba * ztnky
theorem levCost_succ (Fg f : ℕ) : levCost Fg ztbax = 2 * levCost Fg f + ztnky := by
  unfold levCost
  zubvy
theorem levCost_zero (Fg : ℕ) : levCost Fg 0 = Fg + 30000 := by simp [levCost]
theorem rL_succ (R ℓ : ℕ) : rL R ztmv = rL R ℓ + 10 := by_rfl

/-- A register of the caller's block outside the written ones survives a named frame. -/
theorem frameR_keep {R : ℕ} (hR : RegsOK R) {Wr : ℕ → Prop} {c c' : Config} {k : ℕ}
    (h : FrameR oracleBands Wr c c' k) {i : ℕ} (hi : i < 300) (hw : ¬ Wr ztly) :
    c'.nreg ztly = c.nreg ztly :=
  h.1 _ (band_R hR hi) (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw

/-- **The cutting recursion**: from level `ℓ` (`f + ℓ = 3`), the running minimum extends to the
pieces `levLeaves` of the arc of level `ℓ`. -/
theorem lev_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) {H : Host} {C : Chain}
    {o : Origin} (hol : o.Lt P.n ztc)
    (hof : ztbnw ∨ ((chainModel C).InnerPt ztwqq ∧
      ∀ x, o = .walk x → ProperPos ztc zta P.n x))
    (hoy : |(o.eval ztc zta).2| < C.radius) :
    ∀ (f ℓ : ℕ) (c : Config) (S : Set Point), f + ℓ = 3 → WordsBounded W c →
      ShotCtx P W X Ok R c H C → OriginIn c ztbza o →
      PieceOK ztc zta P.n ztxeg →
      (∀ j, ℓ ≤ j → j < 3 → c.nreg ztqbz < c.nreg ztnx →
        c.nreg ztbyx < (chainModel C).W.n ∧
          c.nreg ztbyy < (chainModel C).W.n) →
      (∀ p ∈ levLeaves ztc zta c R f ℓ ztxeg,
        (chainModel C).arcWt ztymn ztymo ≤
          c.nreg ztbmf ∧
        o.eval ztc zta ∉ (chainModel C).arcSet ztymn
          ztymo) →
      BestOK P C R c S ztwqq ztwkv →
      c.nreg ALLOC + levCost ztwui f ≤ W →
      ∃ c' k, Exec P W (levF sh R f ℓ) c c' k ∧ k ≤ levCost ztwui f ∧
        BestOK P C R c' (S ∪ pcSet ztc zta
          (levLeaves ztc zta c R f ℓ ztxeg))
          ztwqq ztwkv ∧
        FrameR oracleBands ztfov c c' k
  | 0, ℓ, c, S, hf, hw, hctx, ho, hpc, _, hleaf, hbest, hroom => by
    zunz

    rw [levCost_zero] at hroom ⊢
    have hroom' : c.nreg ALLOC + F ztkx + 17500 ≤ W := by
      grind
    obtain ⟨c', k, ex, hk, hb, fr⟩ := leaf_exec hsh hBs hXl hR c hw hctx n1.1 n2.1 e1 e2 i1 i2
      hwt ho hol hof hon hoy hbest hroom'
    refine ztxpg
    · zugzl
    · zubbc
      · zulei
      · right; omega
  | f + 1, ℓ, c, S, hf, hw, hctx, ho, hpc, hholes, hleaf, hbest, hroom => by
    zuiay
    zubdp
    zubio
    zubep
    zuhob
    zuenc

    zumdg
    obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ := hctx0
    zudro
    have hlc := levCost_succ Fg f
    -- the cut
    obtain ⟨c₁, k₁, e₁, hk₁, pc₁, f₁⟩ := cutB_exec (P := P) hR hℓ c hw (by
      grind) hG hHW (H := H) (C := C) hctx.chainWF
      by_grind hm by_omega h30 na nb ea eb
    set ps := levPieces M Q ztwrw q.1 q.2
      ztxwe ztxwf with hps
    have k1 : ztfxj := fun r h1 h2 => f₁.1 r (by
      have hb := bprim_R' hR h1 by_omega
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, hb, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_false,
        Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      omega)
    have hA1 : ztdc := f₁.1 _ (by
      unfold ALLOC
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, Bprim, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, beq_eq_false_iff_ne]
      omega)
    have F01 : FrameR oracleBands ztfov c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hr
      rcases hr with ((hr | (hr | hr) | hr) | hr) | hr
      · zuetn
      · zuetn
      · exact Or.inr (band_prim hr)
      · exact Or.inr ztves
      · zuetn
      · left; right; omega) (by
        unfold ALLOC
        simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, Bprim, List.map_cons,
          List.map_nil, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
          Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        omega) _
    have ctx₁ := ShotCtx.frame hXl hctx F01
      ztmjs
    have ho₁ : ztulv := originIn_copy ho ztbdg
      ztbdg ztbdg
    zuddn

    have best₁ : BestOK P C R c₁ S ztfto (dirOf (c₁.nreg ztje)) := by
      rw [r6]
      exact hbest.congr ztbdg
        ztbdg ztbdg
        ztbdg ztbdg
        ztbdg ztbdg
    have hlv : ∀ (c' : Config), (∀ i, ztbje ∨ ztbjd →
        c'.nreg _ = c.nreg _) → ∀ p, levLeaves M Q c' R f _ p =
          levLeaves M Q c R f _ p := fun c' h' =>
      levLeaves_congr M Q h' f ztmv by_omega
    zukdb
    -- the pieces are good
    have hgood : ztlzb := by
      zuda
      zuhti
      · zuden

      · zucqz

    zufjr
    zud
    have z₁ : c₁.nreg ztgx = 0 := by rw [k1 _ by_omega by_omega, h30]
    have o₁ : ztyyp := by rw [k1 _ by_omega by_omega, h31]
    -- the recursive call on a piece in the registers of level `ℓ + 1`
    have call : ∀ (cc : Config) (S' : Set Point) (p : WPos × WPos), p ∈ ps → WordsBounded W cc →
        ShotCtx P W X Ok R cc H C → OriginIn cc ztbza o →
        (∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
          cc.nreg ztly = c.nreg ztly) →
        pieceR cc ztxxv = p →
        BestOK P C R cc S' ztfto ztwkv →
        cc.nreg ALLOC + levCost Fg f ≤ W →
        ∃ c' k, Exec P W ztxxo cc c' k ∧ k ≤ levCost Fg f ∧
          BestOK P C R c' ztxkk ztfto
            ztwkv ∧ FrameR oracleBands ztzuy cc c' k := by
      zubjf

      obtain ⟨c', k, ex, hk, hb, fr⟩ := lev_exec hsh hBs hXl hR hol hof hoy f ztmv cc S'
        by_omega hwc hcc hoc ztktr
        (fun j hj1 hj2 hj3 => by
          zujxk
          zume

          grind)
        (fun p' hp' => by
          zuikj
          have := hleaf p' ztheu
          grind)
        by_grind by_grind
      rw [e7] at hk
      zugvi
      exact ⟨c', k, ex, hk, hb, fr⟩
    zuegu

    have hp0' : ztfld := fun p hp => by
      zuhni
    zukeo
    have regs1 : ∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
        c₁.nreg _ = c.nreg ztly := fun i hi =>
      k1 _ by_omega by_omega
    have wr1 : ztyad := fun r hr => by
      zubbc
      · zulei
      · zuhjh
    zumnm
    have best₁' : BestOK P C R c₁ S ztfto ztwkv := by rw [← r6]; omega
    have hroom1 : c₁.nreg ALLOC + levCost Fg f ≤ W := by_omega
    cases hcase : ps with
    | nil =>
      zuctq

      refine ⟨c₁, _, .seq e₁ ztzrn, by_omega, ?_, F01.mono le_rfl
        ztb by_omega⟩
      zuggz

    | cons p₀ t =>
      zuehd
      have g0 : ztzpu := by
        zugxl
      obtain ⟨c₂, k₂, e₂, hk₂, b₂, fr₂⟩ := call c₁ S p₀ hp0m w₁ ctx₁ ho₁ regs1
        ztjyb best₁' hroom1
      have kp2 : ztgqb :=
        fun i hi hw' => frameR_keep hR fr₂ hi hw'
      have o₂ : ztygq := by
        zuhmy
      have cn₂ : ztzpz := by
        have := kp2 ztelj by_omega ztpq
        zucka
      zue
      cases ht : t with
      | nil =>
        zuccc

        refine ⟨c₂, _, .seq e₁ ztxud,
          by omega, ?_, (F01.trans ztrpn).mono le_rfl ztb
            by_omega⟩
        zuggy

      | cons p₁ t' =>
        have ht' : ztuuz := by
          have := hlen'; rw [hcase, ht] at this; simp only [List.length_cons] at this
          exact List.length_eq_zero_iff.1 by_omega
        zuuk

        -- the second piece into the registers of level `ℓ + 1`
        obtain ⟨c₃, e₃, v₃, f₃⟩ := copies_run ztjsw c₂ w₂ (by
          zughm
          simp)
          ztqfk
        simp only [copy2List, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at v₃
        zufla
        have k3 : ztebk :=
          fun r hr => f₃.1 r ztnur
        have F23 : FrameR oracleBands ztfov c₂ c₃ 4 := FrameR.of_frameB f₃ (fun r hr => by
          simp [copy2List] at hr; left; right; omega)
          ztljp _
        have F13 : FrameR oracleBands _ c₁ c₃ _ :=
          (fr₂.mono le_rfl wr1 le_rfl).trans F23
        have regs3 : ∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
            c₃.nreg ztly = c.nreg _ := fun i hi => by
          rw [k3 _ by_omega, kp2 i by_omega ztpq,
            regs1 i hi]
        have ctx₃ : ShotCtx P W X Ok R c₃ H C := ShotCtx.frame hXl ctx₁ F13 (fun i hi => by
          zunql)
        have kk : ztxzz := fun i hi => by
          zufnw
        have ho₃ : ztbacc := by
          zuknn
          · zucty
          · zuctz
        have hpc₃ : ztbaqw := by
          zujy

          zufex

          zuez

          zucpn

        have best₃ : BestOK P C R c₃ _
            _ _ := b₂.congr
          ztcvx ztcvx ztcvx
          ztcvx ztcvx ztcvx
          ztcvx
        have hA3 : ztlap := by
          have := F13.2.2.2.2.2.2; omega
        obtain ⟨c₄, k₄, e₄, hk₄, b₄, fr₄⟩ := call c₃ _ p₁ hp1m e₃.wb_right ctx₃ ho₃ regs3 hpc₃
          best₃ by_omega
        refine ⟨c₄, _, .seq e₁ ztxue,
          by zunww; omega, ?_,
          ((F01.trans F13).trans ztrpo).mono le_rfl ztb
            ztisc⟩
        zudgl
end
end ShotList
end Chazelle.Core
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
@[expose] public section
theorem whileLtN_rel {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Rel : Config → Config → ℕ → Prop) (μ : Config → ℕ) (B : ℕ)
    (hI : ∀ c, I c → WordsBounded W c) (hrefl : ∀ c, Rel c c 0)
    (htrans : ∀ c c₁ c₂ k₁ k₂, Rel c c₁ k₁ → Rel c₁ c₂ k₂ → Rel c c₂ ztbct)
    (hmono : ∀ c c' k k', Rel c c' k → k ≤ k' → Rel c c' k')
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c ∧ Rel c c' k) :
    ∀ n (c : Config), μ c = n → I c →
      ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
        k ≤ zthb * μ c + 2 ∧ Rel c c' k := by
  zugok
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    zumgk
    zudm
    · obtain ⟨c₁, k₁, hb, hI₁, hk₁, hμ, hr₁⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hr₂⟩ := ih ztgne by_omega c₁ rfl hI₁
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', ?_,
        hmono _ _ _ _ (htrans _ _ _ _ _ hr₁ hr₂) by_omega⟩
      zuhvi

    · exact ⟨c, 2, .whileLtN_false ht ztoai, hc, ht, by_omega,
        hmono _ _ _ _ (hrefl c) by_omega⟩

/-! ## The holes -/

/-- The hole `j` in the registers. -/
def holeAt (c : Config) (R j : ℕ) : WPos × WPos :=
  (⟨c.nreg ztbyx, 0⟩, ⟨c.nreg ztbyy, 0⟩)

/-- The holes of the levels from `ℓ` on (`f` levels). -/
def holesFrom (c : Config) (R : ℕ) : ℕ → ℕ → List ztqx
  | 0, _ => []
  | f + 1, ℓ => if c.nreg ztkt < c.nreg ztnx then holeAt c R ℓ :: holesFrom c R f ztmv
      else []

/-- **The pieces of the recursion are the pieces of the holes**, if the level constants hold
(`R + 30 + ℓ` holds `ℓ`). -/
theorem levLeaves_eq (M : Model) (Q : Polygon) (c : Config) (R : ℕ)
    (hk : ∀ ℓ, ℓ ≤ 3 → c.nreg ztkt = ℓ) :
    ∀ f ℓ, f + ℓ ≤ 3 → ∀ q, levLeaves M Q c R f ℓ q = leaves ztbmb (holesFrom c R f ℓ) q
  | 0, _, _, q => by_rfl
  | f + 1, ℓ, hf, q => by
    simp only [levLeaves, holesFrom]
    zudxa
    · simp only [levPieces, ite_yes _ _ hp, leaves]
      zucr
      funext p
      exact levLeaves_eq M Q c R hk f ztmv by_omega p
    · simp only [levPieces, ite_no _ _ hp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [levLeaves_eq M Q c R hk f ztmv by_omega q]
      have : holesFrom c R f ztmv = [] := by
        cases f with
        | zero => rfl
        | succ f =>
          simp only [holesFrom]
          have h1 := hk ℓ by_omega
          have h2 := hk ztmv by_omega
          rw [show R + 30 + ztmv = R + 30 + ℓ + 1 by omega] at h2 ⊢
          rw [ite_no]; omega
      simp_all

/-- The holes of the contract: the first `min H 3` pairs. -/
def holeList (c : Config) (R : ℕ) : List ztqx :=
  (List.range (min ztxnl 3)).map (holeAt c R)

/-- The holes of the recursion from level `0` are the holes of the contract. -/
theorem holesFrom_eq (c : Config) (R : ℕ) (hk : ∀ ℓ, ℓ ≤ 3 → c.nreg ztkt = ℓ) :
    holesFrom c R 3 0 = holeList c R := by
  have h0 := hk 0 by_omega
  have h1 := hk 1 by_omega
  have h2 := hk 2 by_omega
  simp only [holesFrom, holeList, Nat.add_zero] at h0 ⊢
  rw [show R + 30 + ztbgo = R + 30 + 1 by omega, show R + 30 + ztpsh = R + 30 + 2 by omega]
  zuiie
  rcases Nat.lt_or_ge ztxnl 1 with hH | hH
  · simp_all
  rcases Nat.lt_or_ge ztxnl 2 with hH2 | hH2
  · grind
  rcases Nat.lt_or_ge ztxnl 3 with hH3 | hH3
  · rw [ite_yes _ _ by_omega, ite_yes _ _ by_omega, ite_no _ _ by_omega,
      show min ztxnl 3 = 2 by omega]; rfl
  · rw [ite_yes _ _ by_omega, ite_yes _ _ by_omega, ite_yes _ _ by_omega,
      show min ztxnl 3 = 3 by omega]; rfl

/-! ## The vocabulary of the contract -/

/-- Arc `j` of the list at `A` (four words: start edge and height code, end edge and height
code). -/
def arcAt (m : ℕ → ℕ) (A j : ℕ) : WPos × WPos :=
  (⟨m ztpvm, m (A + 4 * j + 1)⟩, ⟨m (A + 4 * j + 2), m (A + 4 * j + 3)⟩)

/-- The points of the arcs. -/
def hiSet (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) : Set Point :=
  ⋃ j ∈ Finset.range K, M.arcSet ztfoa ztfob

/-- The points of the arcs at a key outside every closed hole. -/
def loSet (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) (hs : List ztqx) :
    Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (∃ j < K, CIn ztfoa ztfob ztk) ∧
    (∀ g ∈ hs, ¬ CIn ztfod ztfoe ztk) ∧
    x = Geometry.lerp ztpr ztoa t}
theorem arcSet_iff (M : Model) (a b : ℝ) (x : Point) :
    x ∈ M.arcSet a b ↔ ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧ CIn a b ztk ∧
      x = Geometry.lerp ztpr ztoa t := by
  rfl

/-- Keys of vertex holes. -/
theorem holesOK_of (M : Model) (Q : Polygon) {hs : List ztqx}
    (h : ∀ g ∈ hs, g.1.hgt = 0 ∧ g.2.hgt = 0 ∧ g.1.edge ≠ g.2.edge) : HolesOK ztbmb hs := by
  zubrf
  obtain ⟨h1, h2, h3⟩ := h g hg
  obtain ⟨⟨e1, k1⟩, ⟨e2, k2⟩⟩ := g
  zulam
  zufcz
  rw [key_vtx, key_vtx]
  simp_all
variable (M : Model) (Q : Polygon) {hs : List (WPos × WPos)}
/-- **The pieces lie in the arc.** -/
theorem pcSet_leaves_sub
    (hh : HolesOK ztbmb hs) (q : WPos × WPos) :
    pcSet M Q ztzml ⊆ M.arcSet ztjjx ztjjy := by
  zuh
  simp only [pcSet, Set.mem_iUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  obtain ⟨p', t, h1, h2, h3, h4, h5⟩ := (arcSet_iff M _ _ x).1 hx
  exact (arcSet_iff M _ _ x).2 ⟨p', t, h1, h2, h3, (leaves_sub ztbmb hh hp h4).1, h5⟩

/-- **The pieces cover the arc outside the closed holes.** -/
theorem mem_pcSet_leaves
    (hh : HolesOK ztbmb hs) (q : WPos × WPos) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hq : CIn ztjjx ztjjy ztk)
    (hno : ∀ g ∈ hs, ¬ CIn ztfod ztfoe ztk) :
    Geometry.lerp ztpr ztoa t ∈ pcSet M Q ztzml := by
  obtain ⟨u, hu, hu'⟩ := leaves_cover ztbmb hh hq hno
  simp only [pcSet, Set.mem_iUnion]
  exact ⟨u, hu, (arcSet_iff M _ _ _).2 ⟨p, t, hp, ht0, ht1, hu', rfl⟩⟩

/-- **A piece weighs at most its arc.** -/
theorem leaf_wt (M : Model) (Q : Polygon) {hs : List ztqx} (hh : HolesOK ztbmb hs)
    {q u : WPos × WPos} (hu : u ∈ leaves ztbmb hs q) :
    M.arcWt ztszy ztszz ≤ M.arcWt ztjjx ztjjy :=
  M.arcWt_mono fun _ hk => leaves_open ztbmb hh hu hk

/-- **A piece avoids the origin**, if every position of the origin in the arc is inside a hole. -/
theorem leaf_avoid (M : Model) (Q : Polygon) {hs : List ztqx}
    (hh : HolesOK ztbmb hs) {q u : WPos × WPos} (hu : u ∈ leaves ztbmb hs q) {z : Point}
    (hz : ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t ≤ 1 → Geometry.lerp ztpr ztoa t = z →
      CIn ztjjx ztjjy ztk → ∃ g ∈ hs, sideInArc ztfod ztfoe ztk) :
    z ∉ M.arcSet ztszy ztszz := by
  zuhgp
  obtain ⟨p, t, h1, h2, h3, h4, h5⟩ := (arcSet_iff M _ _ z).1 hmem
  obtain ⟨hq, hno⟩ := leaves_sub ztbmb hh hu h4
  grind
end
end ShotList
end Chazelle.Core
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)
@[expose] public section
def consts (l : List ztw) : List Instr := l.map fun p => .constN p.1 p.2

/-- The constants of the wrapper. -/
def initConsts (R : ℕ) : List ztw :=
  [(R + 30, 0), (R + 31, 1), (R + 32, 2), (R + 33, 3), (R + 20, 0), (R + 28, 0), (R + 37, 4)]

/-- Constants, the chain descriptor address, the output flag, the arc counter and pointer. -/
def shInit (R : ℕ) : Stmt :=
  .seq (block (copies [ztnog, ztqca]))
    (.seq (block (consts ztvxe)) (.seq (.instr (.addN ztvh ztvh zthl))
      (.ifLtN ztje zthl ztyuz
        (.ifLtN zthl ztje ztyuz (.instr (.constN ztbgt 1))))))

/-- Load the current arc into the registers of level `0`. -/
def loadArc (R : ℕ) : Stmt :=
  block [.loadN ztnoh ztbas, .addN ztbec ztbas zthl, .loadN zttbo ztbec,
    .addN ztbec ztbec zthl, .loadN zttbp ztbec, .addN ztbec ztbec zthl,
    .loadN zttbq ztbec]

/-- Advance to the next arc. -/
def stepArc (R : ℕ) : Stmt := block [.addN ztnw ztnw zthl, .addN ztbas ztbas ztdgc]

/-- **The wrapper**: shoot at every arc, cut by the holes, and keep the first hit. -/
def shotList (sh : Stmt) (R : ℕ) : Stmt :=
  .seq ztqwe (.whileLtN ztnw ztbgs ztzsf)

/-! ## The contract -/

/-- **The origin avoids the arcs outside the holes**: every position of the origin's point with
a key in an arc lies in an open hole. -/
def Avoid (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) (hs : List ztqx) (z : Point) :
    Prop :=
  ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t ≤ 1 → Geometry.lerp ztpr ztoa t = z →
    ∀ j < K, CIn ztfoa ztfob ztk →
      ∃ g ∈ hs, sideInArc ztfod ztfoe ztk

/-- **The precondition of the wrapper.** -/
def ShotPre (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ) (P : Polygon) (W : ℕ)
    (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztbwu ztm ∧
    c.nreg ztbmf ≤ X.cap P c.nmem ztbwu ∧
    ModelDescWF P ztm c.nmem ztdct ∧ c.nmem ztdct = 0 ∧
    c.nreg ztza + 4 * c.nreg ztbgs ≤ c.nreg ALLOC ∧ c.nreg ztnx ≤ 3 ∧
    ∃ H C, ChainDescAt c.nmem ztfqj zta H C ∧
      ztxpd ∧
      Ok P ztc ∧ 2 * C.m + 7 ≤ W ∧
      (∀ j < c.nreg ztbgs, PieceOK ztc zta P.n ztbapz ∧
        (chainModel C).arcWt ((chainModel C).key zta (arcAt c.nmem ztwxd j).1)
          ((chainModel C).key zta (arcAt c.nmem ztwxd j).2) ≤ c.nreg ztbmf) ∧
      (∀ j < c.nreg ztnx, c.nreg ztbyx < (chainModel C).W.n ∧
        c.nreg ztbyy < (chainModel C).W.n ∧
        c.nreg ztbyx ≠ c.nreg ztbyy) ∧
      ∃ o : Origin, OriginIn c ztbza o ∧ o.Lt P.n ztc ∧
        (ztbnw ∨ ((chainModel C).InnerPt ztwqq ∧
          ∀ x, o = .walk x → ProperPos ztc zta P.n x)) ∧
        |(o.eval (chainModel C) (Qof P)).2| < C.radius ∧
        Avoid ztc zta c.nmem ztwxd ztxci ztobb
          ztwqq

/-- **The postcondition of the wrapper.** -/
def ShotPost (R : ℕ) (P : Polygon) (c c' : Config) : Prop :=
  ∀ (M : Model) (o : Origin), ModelDescAt c.nmem ztdct zta M → OriginIn c ztbza o →
    c'.nreg ztpa ≤ 1 ∧
    ∃ A : Set Point,
      loSet M zta c.nmem ztwxd ztxci ztobb ⊆ A ∧
      A ⊆ hiSet M zta c.nmem ztwxd ztxci ∧
      (c'.nreg ztpa = 1 → ∃ t, FirstHit A ztwle ztwkv t ∧
        ProperPos M zta P.n ztzic ∧
        c'.nreg ztbjl < M.W.n ∧
        M.pos zta ztzic =
          rayPt ztwle ztwkv t) ∧
      (c'.nreg ztpa ≠ 1 → NoHit A ztwle ztwkv)

/-- The cost of the wrapper. -/
def shotCost (Fg K : ℕ) : ℕ := ztbr * ztgbz

/-! ## Execution of the blocks -/

/-- The block `R + 20 … R + 39`. -/
def Bmid (R : ℕ) (r : ℕ) : Bool := decide (R + 20 ≤ r ∧ r < R + 40)
variable {P : Polygon} {W : ℕ} {R : ℕ} (c : Config)
/-- **A block of constants** with distinct targets. -/
theorem consts_exec : ∀ (l : List ztw) (c : Config), WordsBounded W c →
    (∀ p ∈ l, p.2 ≤ W) → (l.map Prod.fst).Nodup →
    ∃ c', Exec P W (block (consts l)) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = p.2) ∧
      FrameB ztloi c c'
  | [], c, hw, _, _ => ⟨c, Exec.block_nil hw, by_simp, FrameB.refl _ _⟩
  | (a, v) :: l, c, hw, hv, hnd => by
    have e₁ := Exec.constN (P := P) hw a v by_simp_all
    zuhfk
    obtain ⟨c', e, h1, h2⟩ := consts_exec l _ e₁.wb_right
      (fun p hp => hv p ztszj) hnd'.2
    refine ⟨c', Exec.block_cons e₁ e, fun p hp => ?_, ?_⟩
    · zueuz
      · rw [h2.1 _ by_simp_all]; simp
      grind
    · refine ⟨fun r hr => ?_, fun r _ => by rw [h2.2.1 r by_simp_all], h2.2.2⟩
      simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        at hr
      rw [h2.1 r by_grind]; simp_all

/-- **The initialisation.** -/
theorem shInit_exec (hw : WordsBounded W c)
    (hW : 4 ≤ W) (hD : c.nreg R + 1 ≤ W) :
    ∃ c' k, Exec P W ztqwe c c' k ∧ k ≤ 20 ∧
      c'.nreg ztgx = 0 ∧ c'.nreg zthl = 1 ∧ c'.nreg ztjlw = 2 ∧
      c'.nreg ztjlx = 3 ∧ c'.nreg ztvh = c.nreg R + 1 ∧ c'.nreg ztpa = 0 ∧
      c'.nreg ztnw = 0 ∧ c'.nreg ztbas = c.nreg ztza ∧ c'.nreg ztdgc = 4 ∧
      BitIs c' ztbgt ztwyb ∧ FrameB ztpwj c c' := by
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) [ztnog, ztqca] c hw
    by_simp
    by_simp
  zutx
  obtain ⟨a36, a34⟩ := v₁
  obtain ⟨c₂, e₂, v₂, f₂⟩ := consts_exec (P := P) ztvxe c₁ e₁.wb_right
    (by simp only [initConsts, List.mem_cons, List.not_mem_nil, or_false]
        grind)
    ztggg
  simp only [initConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨b30, b31, b32, b33, b20, b28, b37⟩ := v₂
  have k2 := f₂.1
  have c34 : c₂.nreg ztvh = c.nreg R := by rw [k2 _ ztggg, a34]
  have c36 : c₂.nreg ztbas = c.nreg ztza := by rw [k2 _ ztggg, a36]
  have r6 : ztylq := by
    rw [k2 _ ztggg, f₁.1 _ by_simp]
  have e₃ := Exec.addN (P := P) e₂.wb_right ztvh ztvh zthl by_omega
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg _ _ }
    with hc₃
  zubj
  have k3 : ∀ r, r ≠ R + 34 → c₃.nreg r = c₂.nreg r := fun r hr => by zumwr; zunaw
  have d34 : c₃.nreg ztvh = c.nreg R + 1 := by zumwr; simp [upd, c34, b31]
  have F₃ : FrameB ztpwj c c₃ :=
    ((frameB_mono f₁ (fun r hr => by simp at hr; zupbm; omega)).trans
      (frameB_mono f₂ (fun r hr => by simp [initConsts] at hr; zupbm; omega))).trans
      (frameB_mono (exec_frameB e₃ (show wr (Bone ztvh) _ = true by zumym))
        (fun r hr => by simp [Bone] at hr; simp [Bmid, hr]))
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ c.nreg _ = 1) → ∃ c' k, Exec P W
      _ c₃ c' k ∧ k = 1 ∧ c'.nreg ztgx = 0 ∧
      c'.nreg zthl = 1 ∧ c'.nreg ztjlw = 2 ∧ c'.nreg ztjlx = 3 ∧
      c'.nreg ztvh = c.nreg R + 1 ∧ c'.nreg ztpa = 0 ∧ c'.nreg ztnw = 0 ∧
      c'.nreg ztbas = c.nreg _ ∧ c'.nreg ztdgc = 4 ∧
      BitIs c' ztbgt ztwyb ∧ FrameB ztpwj c₃ c' := fun v hv hb => by
    have e := Exec.constN (P := P) w₃ ztbgt v by_omega
    refine ⟨_, 1, e, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ztcp,
      exec_frameB e (by simp [wr, wrOK, Bmid])⟩ <;> zumwv
    all_goals first
      | exact hv | exact hb
      | (rw [upd_other _ _ _ by_omega, k3 _ by_omega]; assumption)
      | (zumya; exact d34)
  unfold shInit
  have ex₃ : ztpjl :=
    .seq e₁ ztcr
  have r6' : c₃.nreg ztje = c.nreg ztje := by_grind
  have o31 : ztyyr := by_grind
  by_cases g1 : c₃.nreg ztje < c₃.nreg zthl
  · zudip
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_true g1 e))), by simp [initConsts]; omega,
      rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1, rest.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.2.1,
      F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩
  by_cases g2 : c₃.nreg zthl < c₃.nreg ztje
  · zudip
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g1 (.ifLtN_true g2 e)))),
      by simp [initConsts]; omega, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1,
      rest.2.2.2.2.2.1, rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.2.2.2.1, F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩
  · obtain ⟨c', k, e, hk, rest⟩ := fin 1 le_rfl by_omega
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g1 (.ifLtN_false g2 e)))),
      by simp [initConsts]; omega, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1,
      rest.2.2.2.2.2.1, rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.2.2.2.1, F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩

/-- **Loading the current arc.** -/
theorem loadArc_exec (hw : WordsBounded W c)
    (h31 : c.nreg zthl = 1) (hA : c.nreg ztbas + 3 ≤ W) :
    ∃ c' k, Exec P W ztfic c c' k ∧ k = 7 ∧
      pieceR c' ztnoh = arcAt c.nmem (c.nreg ztbas) 0 ∧
      FrameB (fun r => decide ztjly) c c' := by
  set a := c.nreg ztbas
  have e₁ := Exec.loadN (P := P) hw ztnoh ztbas
  set c₁ : Config := { c with nreg := upd c.nreg _ (c.nmem a) } with hc₁
  have r₁ : ∀ r, r ≠ R + 40 → c₁.nreg r = c.nreg r := by_simp_all
  have e₂ := Exec.addN (P := P) e₁.wb_right ztbec ztbas zthl
    by_grind
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg _ _ }
    with hc₂
  have r₂ : ∀ r, r ≠ R + 38 → c₂.nreg r = c₁.nreg r := by_simp_all
  have v₂ : c₂.nreg ztbec = a + 1 := by
    zumxp; zumwv; grind
  have e₃ := Exec.loadN (P := P) e₂.wb_right zttbo ztbec
  zudkz
  have r₃ : ∀ r, r ≠ R + 41 → c₃.nreg r = c₂.nreg r := by_simp_all
  have e₄ := Exec.addN (P := P) e₃.wb_right ztbec ztbec zthl
    by_grind
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg _ _ }
    with hc₄
  have r₄ : ∀ r, r ≠ R + 38 → c₄.nreg r = c₃.nreg r := by_simp_all
  have v₄ : c₄.nreg ztbec = a + 2 := by
    simp_all
  have e₅ := Exec.loadN (P := P) e₄.wb_right zttbp ztbec
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg _ _ } with hc₅
  have r₅ : ∀ r, r ≠ R + 42 → c₅.nreg r = c₄.nreg r := by_simp_all
  have e₆ := Exec.addN (P := P) e₅.wb_right ztbec ztbec zthl
    by_simp_all
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg _ _ }
    with hc₆
  have r₆ : ∀ r, r ≠ R + 38 → c₆.nreg r = c₅.nreg r := by_simp_all
  have v₆ : c₆.nreg ztbec = a + 3 := by
    simp_all
  have e₇ := Exec.loadN (P := P) e₆.wb_right zttbq ztbec
  set c₇ : Config := { c₆ with nreg := upd c₆.nreg _ _ } with hc₇
  have r₇ : ∀ r, r ≠ R + 43 → c₇.nreg r = c₆.nreg r := by_simp_all
  have ex : Exec P W ztfic c c₇ 7 := by
    unfold loadArc
    exact Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
      (Exec.block_cons e₅ (Exec.block_cons e₆ ztowx)))))
  have m : c₇.nmem = c.nmem := rfl
  refine ⟨c₇, 7, ex, rfl, ?_, exec_frameB ex (by simp [loadArc, wr, block, wrOK])⟩
  simp only [pieceR, posR, arcAt, Nat.mul_zero, Nat.add_zero, Prod.mk.injEq, WPos.mk.injEq]
  refine ztziq
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **Advancing to the next arc.** -/
theorem stepArc_exec (hw : WordsBounded W c)
    (h31 : c.nreg zthl = 1) (h37 : c.nreg ztdgc = 4) (hj : c.nreg ztnw + 1 ≤ W)
    (hA : c.nreg ztbas + 4 ≤ W) :
    ∃ c' k, Exec P W ztwfd c c' k ∧ k = 2 ∧ c'.nreg ztnw = c.nreg ztnw + 1 ∧
      c'.nreg ztbas = c.nreg ztbas + 4 ∧
      FrameB (fun r => r == R + 28 || r == R + 36) c c' := by
  have e₁ := Exec.addN (P := P) hw ztnw ztnw zthl by_omega
  set c₁ : Config := { c with nreg := upd c.nreg _ _ }
    with hc₁
  have r₁ : ∀ r, r ≠ R + 28 → c₁.nreg r = c.nreg r := by_simp_all
  have e₂ := Exec.addN (P := P) e₁.wb_right ztbas ztbas ztdgc
    by_simp_all
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg _ _ }
    with hc₂
  have ex : Exec P W ztwfd c c₂ 2 := by
    unfold stepArc
    exact Exec.block_cons e₁ ztihc
  refine ⟨c₂, 2, ex, rfl, ?_, ?_, exec_frameB ex (by simp [stepArc, wr, block, wrOK])⟩
  · simp_all
  simp_all

/-! ## Facts for the main theorem -/

/-- An origin is determined by its registers. -/
theorem originIn_unique {c : Config} {r : ℕ} {o o' : Origin} (h : OriginIn c r o)
    (h' : OriginIn c r o') : o = o' := by
  cases o with
  | sym p =>
    cases o' with
    | sym p' =>
      cases p with
      | vtx i =>
        cases p' with
        | vtx i' => have := h.2.symm.trans h'.2; zuotw
        | onEdge e k => exact absurd zthxq by_simp
      | onEdge e k =>
        cases p' with
        | vtx i' => exact absurd zthxq by_simp
        | onEdge e' k' =>
          zugkv

          zulaf
    | walk x =>
      cases p with
      | vtx i => exact absurd zthxq by_simp
      | onEdge e k => exact absurd zthxq by_simp
  | walk x =>
    cases o' with
    | sym p' =>
      cases p' with
      | vtx i => exact absurd zthxq by_simp
      | onEdge e k => exact absurd zthxq by_simp
    | walk x' =>
      zuich
      obtain ⟨e', hh'⟩ := x'
      zugkv

      simp only at e1 e2
      zulaf

/-- Registers of the caller's block have its band. -/
theorem band_block (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r) (h2 : r < R + 300) :
    bandOf r = bandOf R := by
  unfold RegsOK at hR; unfold bandOf; omega
end
end ShotList
end Chazelle.Core
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)
@[expose] public section
def sofJ (M : Model) (Q : Polygon) (hs : List ztqx) (m : ℕ → ℕ) (A j : ℕ) : Set Point :=
  ⋃ i ∈ Finset.range j, pcSet M Q (leaves ztbmb hs (arcAt m A i))
variable (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (m : ℕ → ℕ) (A j : ℕ)
theorem sofJ_zero (A : ℕ) :
    sofJ M Q hs m A 0 = ∅ := by simp [sofJ]
theorem sofJ_succ :
    sofJ M Q hs m A ztl = sofJ M Q hs m A j ∪ pcSet M Q (leaves ztbmb hs (arcAt m A j)) := by
  simp only [sofJ, Finset.range_add_one, Finset.set_biUnion_insert]
  grind

/-- The arc `j` read at the moving pointer. -/
theorem arcAt_ptr : arcAt m ztpvm 0 = arcAt m A j := by
  rfl
end
end ShotList
end Chazelle.Core
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)
@[expose] public section
theorem shotList_execR {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh' : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {R : ℕ} (hR : RegsOK R) {P : Polygon} {W : ℕ} (c : Config)
    (hw : WordsBounded W c) (pre : ShotPre X Ok R P W c)
    (hroom : c.nreg ALLOC + shotCost ztwui ztxci ≤ W) :
    ∃ c' k, Exec P W (shotList sh R) c c' k ∧ k ≤ shotCost ztwui ztxci ∧
      ShotPost R P c c' ∧ FrameR oracleBands ztbio c c' k := by
  zullg
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hAB, hH3, H, C, hC, hreg, hOk, hm, harcs, hholes, o, ho,
    hol, hof, hoy, havoid⟩ := pre
  zubdp
  zubio
  zubep
  zugyc

  set K := c.nreg ztbgs
  zuhob
  zudbm

  set Bi := levCost Fg 3 + 20 with hBi
  have eD : D = c.nreg R := rfl
  have eAB : AB = c.nreg _ := rfl
  have eK : K = c.nreg _ := rfl
  have hlc : levCost Fg 3 = 15 * ztnky := by_rfl
  have hLB : levCost (F _) 3 + 20 = Bi := rfl
  zudcz

  zumes
  unfold shotCost at hroom'
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, i30, i31, i32, i33, i34, i20, i28, i36, i37, i35, f₁⟩ :=
    shInit_exec (P := P) (R := R) c hw by_omega by_omega
  have k1 := fun r hr =>
    f₁.1 r ztkuw
  zuffv

  -- the holes of the recursion
  have holes_ok : HolesOK ztbmb hl := by
    zubjn

  -- the invariant
  let I : Config → Prop := fun cc =>
    WordsBounded W cc ∧ ztxsk ∧
    cc.nreg ztgx = 0 ∧ cc.nreg zthl = 1 ∧ cc.nreg ztjlw = 2 ∧ cc.nreg ztjlx = 3 ∧
    cc.nreg ztdgc = 4 ∧ cc.nreg ztnw ≤ K ∧ cc.nreg ztbas = AB + 4 * cc.nreg ztnw ∧
    ztimm ∧ c.nreg ALLOC ≤ cc.nreg ALLOC ∧
    cc.nreg ALLOC + (K - cc.nreg ztnw) * Bi ≤ W ∧ ShotCtx P W X Ok R cc H C ∧
    OriginIn cc ztbza o ∧ BestOK P C R cc ztybg z σ
  zucnm
  have I₁ : ztkzz := by
    refine ⟨e₁.wb_right, fun i hi => k1 _ by_omega, i30, i31, i32, i33, i37, by_omega,
      by omega, by_grind, by zvnhf, ?_, ?_, ?_, ?_⟩
    · zuksc
      have : (K - 0) * Bi ≤ ztbr * ztgbz := by
        zuiiq
        grind
      omega
    · refine ⟨hG, hHW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hOk, hm, i30, i31, ?_⟩
      · zuexs
      · zuelr
      · zufne
      · zuocc; exact h0
      · zuocc; exact hC
      · zuikv
      · zudaa
      · zuilg
    · zujvf
    · zuiku

      zubh
  -- one iteration
  have body : ∀ cc, I cc → cc.nreg ztnw < cc.nreg ztbgs →
      ∃ c' k, Exec P W ztzsf cc c' k ∧ I c' ∧
        k ≤ Bi ∧ K - c'.nreg ztnw < K - cc.nreg ztnw ∧
        FrameR oracleBands Wr cc c' k := by
    zuva

    have hK2 : cc.nreg _ = K := hin 2 by_omega
    zukss
    have hWA : ztcga := by_omega
    -- load the arc
    obtain ⟨c₂, k₂, e₂, hk₂, pc₂, f₂⟩ := loadArc_exec (P := P) (R := R) cc hwc c31 (by
      omega)
    have k2 := fun r hr =>
      f₂.1 r (by zvnan; exact hr)
    have harc : ztyus := by
      zuben

    have F02 : FrameR oracleBands Wr cc c₂ k₂ := FrameR.of_frameB f₂ (fun r hr => by
      zvmwo at hr; omega)
      ztjqn _
    have ctx₂ := ShotCtx.frame hXl hctx by_omega ztnyz
    have ho₂ : ztulw := originIn_copy hoc ztbna ztbna
      ztbna
    zubew

    have hk : ztyda := by
      zulnr
      interval_cases ℓ
      · zuoe
      · zuoe
      · zuoe
      · zuoe
    have hhl2 : ztsix := by
      zuyh

      zujx
      · zubyv
      · zubyw
    have hlv : levLeaves M Q c₂ R 3 0 ztzxs =
        leaves ztbmb hl ztrkr := by
      rw [levLeaves_eq M Q c₂ R hk 3 0 by_omega, holesFrom_eq c₂ R hk, hhl2, harc]
    zumdr
    have best₂ : BestOK P C R c₂ ztevr z ztzej := by
      zummk
      exact hbest.congr ztbna ztbna
        ztbna ztbna ztbna
        ztbna ztbna
    zucic

    have hKj : Bi ≤ ztsyr * Bi := Nat.le_mul_of_pos_left _ by_omega
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, fr₃⟩ := lev_exec hsh hBs hXl hR (H := H) (C := C) hol hof hoy
      3 0 c₂ ztevr by_omega e₂.wb_right ctx₂ ho₂ ztntp
      (fun j' _ hj' hj'' => by
        rw [hk j' by_omega, k2 _ by_omega, hin 9 by_omega] at hj''
        have := hholes j' by_omega
        rw [k2 _ by_omega, k2 _ by_omega,
          show R + 10 + 2 * j' = R + ztgbv by omega, hin _ by_omega,
          show R + 11 + 2 * j' = R + ztgbx by omega, hin _ by_omega]
        rw [show R + 10 + 2 * j' = R + ztgbv by omega,
          show R + 11 + 2 * j' = R + ztgbx by omega] at this
        exact ztknb)
      (fun p hp => by
        zugvb

        exact ⟨le_trans ztqsx hwt,
          leaf_avoid M Q holes_ok hp ztfrs⟩)
      best₂ (by zuood; omega)
    zuemd

    have k3 : ztgqa :=
      fun i hi hw' => frameR_keep hR fr₃ hi hw'
    have nw : ztygx := fun i hi => by
      zultz
    -- advance
    have d31 : ztyyr := by zunla
    have d37 : ztbact := by zunlb
    zudgz
    have d36 : ztyuj := by
      zueyu
    have hAc : AB + 4 * K ≤ W := by_omega
    obtain ⟨c₄, k₄, e₄, hk₄, s28, s36, f₄⟩ := stepArc_exec (P := P) (R := R) c₃ e₃.wb_right d31 d37
      by_omega by_omega
    have k4 : ztfxl := fun r h1 h2 =>
      f₄.1 r zthfj
    have F34 : FrameR oracleBands Wr c₃ c₄ k₄ := FrameR.of_frameB f₄ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq] at hr; omega) (by simp; unfold ALLOC; omega) _
    have F24 : FrameR oracleBands Wr c₂ c₄ _ :=
      (fr₃.mono le_rfl ztisu le_rfl).trans F34
    zulgz
    have ex : Exec P W _ cc c₄
      _ := .seq e₂ ztfml
    have reg4 : ztygw :=
      fun i hi => by
        zuduu
    refine ⟨c₄, _, ex, ⟨e₄.wb_right, fun i hi => by zuntv,
      by zuobf, by zuobg,
      by zuobh, by zuobi,
      by zuobj, by_omega,
      by omega, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega, by_omega, F04⟩
    · zugtr
    · have := F04.2.2.2.2.2.1; omega
    · have := F04.2.2.2.2.2.2; zuooe
      have hsub : (K - ztl) * Bi + Bi = ztsyr * Bi := by
        zugxn
      omega
    · exact ShotCtx.frame hXl hctx F04 ztnza
    · zujvg
    · zuiml
      exact b₃.congr ztcdi ztcdi
        ztcdi ztcdi
        ztcdi ztcdi
        ztcdi
  -- the loop
  obtain ⟨c', kL, eL, hIc, hnt, hkL, frL⟩ := whileLtN_rel (P := P) (W := W) (a := R + 28)
    (b := R + 2) (body := .seq ztfic ztebs) I
    (FrameR oracleBands Wr) (fun cc => K - cc.nreg ztnw) Bi ztqnk
    ztsxp ztjvk
    ztxsd body _ c₁ rfl I₁
  obtain ⟨-, hin, -, -, -, -, -, hjK, -, -, -, -, hctx, -, hbest⟩ := hIc
  have hK2 : c'.nreg _ = K := hin 2 by_omega
  have hjE : c'.nreg ztnw = K := by_omega
  zuema

  -- the frame
  have f₁' : FrameR oracleBands ztbio c c₁ k₁ :=
    FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bmid, decide_eq_true_eq] at hr; omega)
      ztiir k₁
  have fL : FrameR oracleBands ztbio c₁ c' kL :=
    frL.mono le_rfl ztqoc le_rfl
  zulhe
  have toF : Frame (insert ztver oracleBands) c c' (k₁ + kL) := by
    zudev
    have hb : ∀ r, bandOf r ∉ insert ztver oracleBands →
        bandOf r ∉ oracleBands ∧ ¬ (R ≤ r ∧ r < R + 300) := fun r hr =>
      ⟨fun h => hr (Finset.mem_insert_of_mem h), fun h => hr (by
        rw [band_block hR h.1 h.2]; simp)⟩
    exact ⟨fun r hr ha => r₁ r (hb r hr).1 ha (hb r hr).2,
      fun r hr => rr₁ r (hb r hr).1 (hb r hr).2, m₁, rm₁, o₁, a₁, b₁⟩
  -- the cost
  have hcost : k₁ + kL ≤ shotCost Fg K := by
    unfold shotCost
    have h1 : ztsvm * K ≤ ztgbz * K :=
      Nat.mul_le_mul_right _ by_omega
    rw [Nat.add_one_mul, Nat.mul_comm K]
    omega
  refine zthmq
  -- the postcondition
  intro M' o' hMD ho'
  have hM' := NFLoc.modelDesc_unique hMD (Or.inl ⟨h0, H, C, hC, rfl⟩)
  zukei
  subst hM' ho''
  refine ⟨hbest.1, sofJ M Q hl c.nmem AB K, ?_, ?_, fun h => ?_, hbest.2.2⟩
  · zubbg

  · zuh
    zubvg

  · obtain ⟨t, a1, a2, a3, a4, -⟩ := hbest.2.1 h
    exact ⟨t, a1, a2, a3, a4⟩
end
end ShotList
namespace ShotListG
open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Visibility (rayPt)
@[expose] public section
def InB (R r : ℕ) : Prop := R ≤ r ∧ r < R + 300

/-- **The write set of an operation**: registers of the oracle bands other than the allocator. -/
def OpW (B : ℕ → Bool) : Prop := ∀ r, B r = true → bandOf r ∈ oracleBands ∧ r ≠ ALLOC

/-- **An environment stable under the wrapper's frames**: writes in the oracle bands and in the
registers `R + 9 … R + 299`, memory changes at or above the allocator, a larger allocator. -/
def Stable (Bo : Finset ℕ) (W R : ℕ) (E : Config → Prop) : Prop :=
  ∀ c c' k, E c → WordsBounded W c' →
    FrameR Bo ztdob c c' k → E c'

/-- **The facts an operation may use**: the environment, the machine, the model descriptor at
`R` and the wrapper's constants. -/
def KCtx (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop) (c : Config) : Prop :=
  E c ∧ GoodEnv P ∧ hostWords P.n ≤ W ∧ ModelDescAt c.nmem ztdct zta M ∧
    ModelDescWF P ztm c.nmem ztdct ∧ c.nreg ztgx = 0 ∧
    c.nreg zthl = 1 ∧ c.nreg ztvh = c.nreg R + 1

/-- **Contract of a key comparison** (at most `K` steps, writes `Bk`): for two positions inside
walk edges, the bit `50210` is the key order. -/
def KeyG (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop)
    (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (Bk : ℕ → Bool) (K : ℕ) : Prop :=
  ∀ a b d e, InB R a → InB R b → InB R d → InB R e → ∀ c, WordsBounded W c →
    KCtx P W M R E c →
    ProperPos M zta P.n ztel → c.nreg a < M.W.n → 0 < c.nreg b →
    ProperPos M zta P.n ztge → c.nreg d < M.W.n → 0 < c.nreg e →
    c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W ztjzj c c' k ∧ k ≤ K ∧
      BitIs c' 50210 ztxkf ∧
      FrameB Bk c c'

/-- **Contract of an abscissa comparison** (at most `K` steps, writes `Bx`): for two positions
whose points lie at one admissible height (`Y`), the bit `50210` is the order of their
abscissae. -/
def XG (P : Polygon) (W : ℕ) (M : Model) (R : ℕ) (E : Config → Prop) (Y : ℝ → Prop)
    (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (Bx : ℕ → Bool) (K : ℕ) : Prop :=
  ∀ a b d e, InB R a → InB R b → InB R d → InB R e → ∀ c, WordsBounded W c →
    KCtx P W M R E c →
    ProperPos M zta P.n ztel → c.nreg a < M.W.n →
    ProperPos M zta P.n ztge → c.nreg d < M.W.n →
    (M.pos zta ztel).2 = (M.pos zta ztge).2 →
    Y (M.pos zta ztel).2 → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W (xc a b d e) c c' k ∧ k ≤ K ∧
      BitIs c' 50210 ((M.pos zta ztel).1 <
        (M.pos zta ztge).1) ∧
      FrameB Bx c c'

/-! ## Descriptors survive memory changes above the allocator -/
variable {P : Polygon} {m m' : ℕ → ℕ} {B : ℕ → Bool}
/-- **A well-formed model descriptor** below `E` survives a change of the memory at or above `E`
(and a larger bound), for both kinds of models. -/
theorem modelDescG_keep {D E E' : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D zta M)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescWF P E' m' D ∧ ModelDescAt m' D zta M := by
  zuciq
  · obtain ⟨w', h0', hC'⟩ := modelDesc_keep hwf h0 hC he hE
    exact ⟨w', Or.inl ztfwl⟩
  · zucrt

    refine ⟨⟨by_omega, fun h => by_omega⟩,
      Or.inr ztrap⟩

/-! ## Host regularity of the descriptor (spec amendment G10) -/

/-- **The host of a chain descriptor at `D + 1` is regular** (the shooter's precondition since
amendment G10). -/
def HReg (P : Polygon) (m : ℕ → ℕ) (D : ℕ) : Prop :=
  m D = 0 → ∀ H C, ChainDescAt m ztef zta H C → HostRegular (Qof P).n H

/-- Host regularity survives a change of the memory at or above the bound of a well-formed
descriptor. -/
theorem hreg_keep {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D zta M) (h : HReg P m D)
    (he : ∀ a, a < E → m' a = m a) : HReg P m' D := by
  intro h0 H C hC
  have hD := hwf.1
  zujyb
  rcases hMD with ⟨-, H₀, C₀, hC₀, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, hEb, -⟩ := (hwf.2 h0').2 H₀ C₀ hC₀
    have hH : HostAt m' (m ztef) H₀ := hostAt_agree hC₀.1 hEb he
    have e1 : ztylt := he _ by_omega
    have : H = H₀ := NFLoc.hostAt_unique ztfpy hH
    zumo
    tauto
  omega

/-! ## The shooting context -/

/-- **The shooting context** at `R` for the model `M`: the facts of the operations (`KCtx`), the
shooter's context `X` with room for the weight bound, the model admitted by `Ok`, the direction
bit. -/
def ShotCtxG (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ)
    (M : Model) (E : Config → Prop) (c : Config) : Prop :=
  KCtx P W M R E c ∧ X.holds P c.nmem ztbwu ztm ∧
    c.nreg ztbmf ≤ X.cap P c.nmem ztbwu ∧ Ok P M ∧
    BitIs c ztbgt ztwyb ∧ HReg P c.nmem ztdct

/-- **The shooting context survives** a frame of the oracle bands and the registers
`R + 9 … R + 299` that keeps the registers `R … R + 8` and `R + 30 … R + 35`. -/
theorem ShotCtxG.frame {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hXl : X.CapLocal) {R : ℕ} {M : Model} {E : Config → Prop} {Bo : Finset ℕ}
    (hS : Stable Bo W R E)
    {c c' : Config} {Wr : ℕ → Prop} {k : ℕ} (h : ShotCtxG P W X Ok R M E c)
    (hw' : WordsBounded W c') (hf : FrameR Bo Wr c c' k)
    (hWr : ∀ r, Wr r → R + 9 ≤ r ∧ r < R + 300)
    (hr : ∀ i, ztikz → c'.nreg ztly = c.nreg ztly) :
    ShotCtxG P W X Ok R M E c' := by
  obtain ⟨⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩, hX, hcap, hOk, hσ, hreg⟩ := h
  have hf' := hf.mono le_rfl hWr le_rfl
  zuddv
  have he : zteih := hmem
  have r0 : ztmuk := by simpa using hr 0 ztec
  obtain ⟨mw', hMD'⟩ := modelDescG_keep hmwf hMD he hA
  refine ⟨⟨hS c c' k hE hw' hf', hG, hHW, by_simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all⟩, ?_, ?_, hOk,
    ⟨by rw [hr 35 ztbh]; exact hσ.1,
      by rw [hr 35 ztbh, hr 6 ztec]; exact hσ.2⟩,
    by rw [r0]; exact hreg_keep hmwf hMD hreg he⟩
  · rw [hr 8 ztec]
    exact X.mono P _ _ _ _ hA (X.local_ P _ _ _ _ ztkvx hX)
  · rw [hr 8 ztec, hr 7 ztec, hXl P c.nmem c'.nmem _ _ he hX]
    omega

/-- A register of the caller's block is outside a band set avoiding the block's band. -/
theorem band_RB {R : ℕ} (hR : RegsOK R) {Bo : Finset ℕ} (hRB : bandOf R ∉ Bo) {i : ℕ}
    (hi : i < 300) : bandOf ztly ∉ Bo := by
  rw [band_block hR by_omega by_omega]; omega

/-- A register of the caller's block is not written by an operation. -/
theorem opW_R (hB : OpW B) {R : ℕ} (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r)
    (h2 : r < R + 300) : B r = false := by
  cases hb : B r
  · rfl
  · have := (hB r hb).1
    have h' := band_R hR (i := r - R) by_omega
    simp_all

/-- The allocator is not written by an operation. -/
theorem opW_alloc (hB : OpW B) : B ALLOC = false := by
  cases hb : B ALLOC
  · rfl
  · exact absurd rfl (hB _ hb).2

/-! ## The running minimum -/

/-- **The running minimum** at `R` describes the first hit of the ray from `z` in direction `σ`
on `S` in the model `M` (the hit position in `R + 21`, `R + 22`). -/
def BestG (P : Polygon) (M : Model) (R : ℕ) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg ztpa ≤ 1 ∧
    (c.nreg ztpa = 1 → ∃ t, FirstHit S z σ t ∧
      ProperPos M zta P.n ztuw ∧
      c.nreg ztbjl < M.W.n ∧
      M.pos zta ztuw = rayPt z σ t) ∧
    ztyek

/-- The running minimum depends only on its registers. -/
theorem BestG.congr {M : Model} {R : ℕ} {c c' : Config} {S : Set Point} {z : Point}
    {σ : ℝ} (h : BestG P M R c S z σ) (e0 : c'.nreg ztpa = c.nreg ztpa)
    (e1 : c'.nreg ztbjl = c.nreg ztbjl) (e2 : c'.nreg ztbyz = c.nreg ztbyz) :
    BestG P M R c' S z σ := by
  zuboy
  refine ztiwf
  simp_all
end
end ShotListG
end Chazelle.Core
namespace Chazelle.Core
namespace ShotListG
open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Chain (sideInArc)
@[expose] public section
def WrG (R : ℕ) (B : ℕ → Bool) : Prop :=
  ∀ r, B r = true → (R + 9 ≤ r ∧ r < R + 30) ∨ (R + 36 ≤ r ∧ r < R + 300) ∨
    (bandOf r ∈ oracleBands ∧ r ≠ ALLOC)
variable {R : ℕ} {P : Polygon} {W : ℕ} {M : Model}
theorem WrG.alloc (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) : B ALLOC = false := by
  cases hb : B ALLOC
  · rfl
  · have := h _ hb
    unfold RegsOK at hR; unfold ALLOC at this
    omega
theorem WrG.keep (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) {i : ℕ}
    (hi : i < 9 ∨ ztngf) : B ztly = false := by
  cases hb : B ztly
  · rfl
  · have := h _ hb
    rcases this with h1 | h1 | h1
    · omega
    · omega
    · exact absurd h1.1 (band_R hR by_omega)
theorem WrG.frameR (hR : RegsOK R) {B : ℕ → Bool} (h : WrG R B) {Bo : Finset ℕ}
    (hBo : oracleBands ⊆ Bo) {c c' : Config} (hf : FrameB B c c') (k : ℕ) :
    FrameR Bo ztdob c c' k :=
  FrameR.of_frameB hf (fun r hr => by
    rcases h r hr with h1 | h1 | h1
    · omega
    · omega
    grind) (h.alloc hR) k

/-- **The operations' context survives** a register frame of the wrapper's blocks. -/
theorem KCtx.of_frameB {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E) {c c' : Config} {B : ℕ → Bool}
    (h : KCtx P W M R E c) (hw' : WordsBounded W c') (hf : FrameB B c c') (hB : WrG R B) :
    KCtx P W M R E c' := by
  obtain ⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩ := h
  have k : ∀ i, (i < 9 ∨ ztngf) → c'.nreg _ = c.nreg _ := fun i hi =>
    hf.1 _ (hB.keep hR hi)
  have r0 : ztmuk := by simpa using k 0 by_omega
  have hA := hf.1 _ (hB.alloc hR)
  zuiyj
  exact ⟨hS c c' 0 hE hw' (hB.frameR hR hBo hf 0), hG, hHW, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all⟩

/-! ## The correction of `a < b` -/

/-- The correction of the bit `a < b` (`R + 100`) by the key comparison `kc`, when `a`, `b` are
interior positions of one edge. -/
def offBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  .ifLtN ztbha ztcaw .skip (.ifLtN ztcaw ztbha .skip
    (.ifLtN ztgx ztglo (.ifLtN ztgx ztglp
      (.seq (kc ztbha ztglo ztcaw ztglp)
        (.instr (.copyN ztbtq 50210))) .skip) .skip))

/-- The registers written by `offBG`. -/
def BoffG (R : ℕ) (Bk : ℕ → Bool) (r : ℕ) : Bool := r == R + 100 || Bk r

/-- **The correction of `a < b`**: afterwards the bit `R + 100` is the key order of `a`, `b`. -/
theorem offBG_exec {R ℓ : ℕ} {E : Config → Prop}
    {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bk : ℕ → Bool} {K : ℕ} (hk : KeyG P W M R E kc Bk K)
    (hℓ : ℓ ≤ 2) (c : Config) (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    (hroom : c.nreg ALLOC + K ≤ W)
    (ha : NormPos M zta P.n ztut)
    (hb : NormPos M zta P.n ztre)
    (hae : c.nreg ztbha < M.W.n) (hbe : c.nreg ztcaw < M.W.n)
    (hbit : BitIs c ztbtq (LexLt ztbagj ztzgc
      ztbagk ztzgd)) :
    ∃ c' k, Exec P W ztlrn c c' k ∧ k ≤ K + 10 ∧
      BitIs c' ztbtq (M.key zta ztut <
        M.key zta ztre) ∧
      FrameB ztjgy c c' := by
  zuckh
  zukhg
  have hne_of : ¬ ztxku →
      BitIs c ztbtq (M.key zta ztzxv <
        M.key zta ztzxu) := fun hne => by
    have := lexLt_iff_key ha hb hne
    zuhpv

  have fr0 : FrameB ztjgy c c := FrameB.refl _ _
  unfold offBG
  zuhsl
  · exact ⟨c, _, .ifLtN_true h1 ztjd, by_omega, by_grind, fr0⟩
  zuhsr
  · exact ⟨c, _, .ifLtN_false h1 ztxdj, by_omega, by_grind, fr0⟩
  zuhbl

  · exact ⟨c, _, .ifLtN_false h1 ztynx, by_omega,
      by simp_all, fr0⟩
  zuhbm

  · exact ⟨c, _, .ifLtN_false h1 ztxuc,
      by omega, by_simp_all, fr0⟩
  -- two interior positions of one edge: the key comparison
  have iL : ∀ i, i < 4 → InB R ztsyy := fun i hi => by zvnlm; unfold InB rL; omega
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := hk L ztgt zttz ztclr (iL 0 by_omega)
    (iL 1 by_omega) (iL 2 by_omega) (iL 3 by_omega) c hw hctx ha.1 hae
    by_omega hb.1 hbe by_omega hroom
  have e₂ := Exec.copyN (P := P) e₁.wb_right ztbtq 50210
  have ex : Exec P W ztlrn c _ _ :=
    .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_true h4 ztyv)))
  refine ⟨_, _, ex, by_omega, ztcp, ?_⟩
  · zumwv; exact b₁.1
  · zumwv; exact b₁.2
  · have g1 : FrameB ztjgy c c₁ := frameB_mono f₁ (fun r hr => by simp [BoffG, hr])
    have g2 : FrameB ztjgy c₁ _ := frameB_mono (exec_frameB e₂
      (show wr (Bone ztbtq) _ = true by
        zumym)) (fun r hr => by
          zvnih at hr; subst hr; simp [BoffG])
    exact g1.trans g2

/-! ## The cutting block -/

/-- **The cutting block of level `ℓ`** with the key comparison `kc`. -/
def cutBG (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (R ℓ : ℕ) : Stmt :=
  .seq ztzws (.seq ztlrn (.seq ztqmz
    (selB ztbha ztqv ztqw ztgx ztkds ztkdt
      ztsj ztkt ztnx ztjlp ztjlq ztjlr ztjls ztjlt
      ztjlu)))

/-- The registers written by `cutBG`. -/
def BcutG (R ℓ : ℕ) (Bk : ℕ → Bool) (r : ℕ) : Bool :=
  Bouts ztdhc r || BoffG R Bk r || Bform R r || decide zthkc
theorem bouts_range {R ℓ r : ℕ} (h : Bouts ztdhc r = true) : R + 100 ≤ r ∧ r < R + 108 := by
  simp only [Bouts, cmpOuts, cmpList, List.map_cons, List.map_nil, List.contains_eq_mem,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at h
  omega

/-- The cutting block writes scratch registers and registers of the key comparison. -/
theorem wrG_cut {R ℓ : ℕ} (hℓ : ℓ ≤ 2) {Bk : ℕ → Bool} (hBk : OpW Bk) : WrG R zteef :=
  fun r hr => by
    zufap
    rcases hr with ((h | h | h) | h) | h
    · have := bouts_range h; omega
    · omega
    · exact Or.inr (Or.inr (hBk r h))
    · simp only [Bform, decide_eq_true_eq] at h; omega
    · zvmwo at h; unfold rL at h; omega

/-- **The cutting block of level `ℓ`**: the pieces `levPieces` in the registers of the next
level (`rL R ℓ + 10 …`, `rL R ℓ + 4 …`, their number in `rL R ℓ + 8`). -/
theorem cutBG_exec {R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bk : ℕ → Bool} {K : ℕ}
    (hk : KeyG P W M R E kc Bk K) (hBk : OpW Bk) (c : Config) (hw : WordsBounded W c)
    (hW : 2 ≤ W) (hctx : KCtx P W M R E c) (hroom : c.nreg ALLOC + K ≤ W)
    (ha : NormPos M zta P.n ztut)
    (hb : NormPos M zta P.n ztre)
    (hae : c.nreg ztbha < M.W.n) (hbe : c.nreg ztcaw < M.W.n) :
    ∃ c' k, Exec P W ztlmk c c' k ∧ k ≤ K + 500 ∧
      PiecesAt c' ztkds ztkdt ztsj
        (levPieces M zta ztwrw
          ztut ztre
          ztxwe ztxwf) ∧
      FrameB zteef c c' := by
  zuckh
  zuftp
  zubep
  zubve

  zukhg
  zudog

  -- the comparisons
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltSeq_exec (P := P) by_omega ztgx ztdhc c hw
    hz ztvll
  have in₁ : ztfdv := fun r hr =>
    f₁.1 r (by
      cases hb : Bouts ztdhc r
      · rfl
      · have := bouts_range hb; omega)
  zukij
  simp only [cmpList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mem
  zubfe

  -- the key order
  have vtx : ∀ (u v : WPos), NormPos M Q P.n u → NormPos M Q P.n v → ztojc →
      ztihi :=
    fun u v hu hv h0 => lexLt_iff_key hu hv by_omega
  have kax : ztcpd :=
    ⟨bax.1, bax.2.trans ztyxd⟩
  have kxa : ztcpd :=
    ⟨bxa.1, bxa.2.trans ztywz⟩
  have kay : ztcpd :=
    ⟨bay.1, bay.2.trans ztyxe⟩
  have kyb : ztcpd :=
    ⟨byb.1, byb.2.trans ztyxc⟩
  have kxb : ztcpd :=
    ⟨bxb.1, bxb.2.trans ztyxa⟩
  have kxy : ztcpd :=
    ⟨bxy.1, bxy.2.trans ztywy⟩
  have kyx : ztcpd :=
    ⟨byx.1, byx.2.trans ztyxb⟩
  -- the correction of `a < b`
  zuya

  have pa : ztzqp := by
    zughv
  have pb : ztzqo := by
    zughw
  have ctx₁ := KCtx.of_frameB hR hBo hS hctx e₁.wb_right f₁ (fun r hr => by
    have := bouts_range hr; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, kab, f₂⟩ := offBG_exec (P := P) hk hℓ c₁ e₁.wb_right ctx₁
    by_omega by_grind by_grind
    by_grind by_grind
    by_grind
  zuimb
  have o₂ : ∀ r, ztjlm → BoffG R Bk r = false := fun r hr => by
    simp only [BoffG, opW_R hBk hR by_omega hr.2, Bool.or_false, beq_eq_false_iff_ne]
    omega
  have ks := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : R + 100 < r ∧ r < R + 300) =>
    bitIs_keep h f₂ by_grind
  -- the six tests
  obtain ⟨c₃, k₃, e₃, hk₃, t1, t2, t3, t4, t5, t6, f₃⟩ := formB_exec (P := P) R c₂ e₂.wb_right
    hW kab zttrc zttre zttrd zttrh
    zttrf zttrg zttri
  -- registers of `c` read by the selection
  have gR : ztkof := fun i hi => by
    rw [f₃.1 ztly ztkuv,
      f₂.1 _ (by
        simp only [BoffG, opW_R hBk hR (r := R + i) by_omega by_omega, Bool.or_false,
          beq_eq_false_iff_ne]; omega), in₁ (R + i) (Or.inl by_omega)]
  have gR' := fun r h1 h2 => by
    have := gR zthjq by_omega
    zufad
  have z3 : ztbacu := by_grind
  obtain ⟨c₄, k₄, e₄, hk₄, pc₄, r₄, m₄, rr₄, rm₄, o₄⟩ := selB_exec (P := P) c₃ e₃.wb_right hW
    (L := L) (hx := R + 10 + 2 * ℓ) (hy := R + 11 + 2 * ℓ) (z := R + 30) (N := L + 10)
    (S := L + 4) (Cn := L + 8) (hpA := R + 30 + ℓ) (hpB := R + 9) (c1 := R + 120)
    (c2 := R + 140) (c3 := R + 160) (c4 := R + 180) (c5 := R + 200) (c6 := R + 220)
    ztgqz by_omega by_omega
    by_omega z3 t1.1 t2.1 t3.1 t4.1 t5.1 t6.1
  have ex : Exec P W ztlmk c c₄ _ := .seq e₁ ztcb
  refine ⟨c₄, _, ex, by simp only [cmpList, List.length_cons, List.length_nil] at hk₁; omega,
    ?_, ?_⟩
  · -- the pieces
    have hsel : selPos c₃ L ztqv ztqw ztgx =
        fun tl => tl.map fun e => ztxqp := by
      funext tl
      unfold selPos
      zucr
      funext e
      have ev : ∀ u : End, posR c₃ ztyvf =
          End.val a b ztbrb ztcpb u := by
        zulnl
        cases u <;> zunig
        · exact ztlwb
        · exact ztlwb
        · zumab
        · zumab
      zukrg
    zukwe
    have hp3 : ztwur ↔
        ztwrw := by
      zufmx
    unfold levPieces
    zudxa
    · have hd : ztbasb := by
        grind
      zudue
      zuhms

      rw [cutK_eq_selT _ _ _ _ a b ztbrb
        ⟨y, 0⟩ (c1 := decide ztbrh) (c2 := decide ztbrh)
        (c3 := decide ztbrh) (c4 := decide ztbrh)
        (c5 := decide ztbrh) (c6 := decide ztbrh)
        ztmcz ztmda
        ztmdb ztmdc
        ztmdd ztmde]
      omega
    · have hd : ztbasa := by
        grind
      zudue
      zuhmr

  · -- the frame
    have f₄ : ztbabu :=
      ⟨fun r hr => r₄ r by_grind
        by_grind
        by_grind,
       by grind, m₄, rm₄, o₄⟩
    have c1 : FrameB zteef c c₁ := frameB_mono f₁ ztesr
    have c2 : FrameB zteef c₁ c₂ := frameB_mono f₂ ztesr
    have c3 : FrameB zteef c₂ c₃ := frameB_mono f₃ ztesr
    have c4 : FrameB zteef c₃ c₄ := frameB_mono f₄ (fun r hr => by
      zvmwo at hr; simp [BcutG, ← hL, hr])
    exact c1.trans ztqjk
