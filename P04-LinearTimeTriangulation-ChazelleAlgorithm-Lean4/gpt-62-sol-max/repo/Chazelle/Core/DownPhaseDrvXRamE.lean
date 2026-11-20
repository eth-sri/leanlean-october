module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.DownPhaseDrvXRamD

/-!
# Down phase, extraction (D6), RAM part 5: the bucket loop

* `bktBody_exec`: one arc of the region: if no arc was found yet and the position lies on the
  closure of this arc (`OnArcP`), the bucket `bktF` of the position for this arc;
* `bktS_exec`: the loop over the arcs of the region.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)

@[expose] public section

/-- The registers `bktS` writes. -/
def Bbkt (r : ℕ) : Bool :=
  decide ((217112 ≤ r ∧ r ≤ 217128) ∨ (217150 ≤ r ∧ r ≤ 217156) ∨ (217160 ≤ r ∧ r ≤ 217162))

theorem wr_bktBody : wr Bbkt bktBody = true := by decide

/-- The registers `posLtOn … dst` writes. -/
def Bon (dst r : ℕ) : Bool :=
  decide ((217150 ≤ r ∧ r ≤ 217156) ∨ (217160 ≤ r ∧ r ≤ 217162) ∨ r = dst)

open Classical in
theorem onArc_bits (Q : Polygon) (li : Bool) (N : NF) (j : ℕ) (x : WPos) :
    (if (if PosEq x (N.arc j).s then 1 else 0) < 1 then
      (if (if PosEq x (N.arc j).e then 1 else 0) < 1 then
        (if (if PosLt Q li (N.arc j).s (N.arc j).e then 1 else 0) < 1 then
          (if (if PosLt Q li (N.arc j).s x then 1 else 0) < 1 then
            (if (if PosLt Q li x (N.arc j).e then 1 else 0) < 1 then 0 else 1) else 1)
        else (if (if PosLt Q li (N.arc j).s x then 1 else 0) < 1 then 0 else
          (if (if PosLt Q li x (N.arc j).e then 1 else 0) < 1 then 0 else 1)))
      else 1) else 1 : ℕ) = if OnArcP Q li N j x then 1 else 0 := by
  unfold OnArcP
  by_cases p1 : PosEq x (N.arc j).s <;> by_cases p2 : PosEq x (N.arc j).e <;>
    by_cases p3 : PosLt Q li (N.arc j).s (N.arc j).e <;> by_cases p4 : PosLt Q li (N.arc j).s x <;>
    by_cases p5 : PosLt Q li x (N.arc j).e <;> simp_all

open Classical in
theorem bktF_bits (A j : ℕ) (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    (if (if a then 1 else 0) < 1 then (if (if b then 1 else 0) < 1 then
        (if (if c then 1 else 0) < 1 then 0 else 2 * j + 2) else 2 * ((j + 1) % A) + 1)
      else 2 * j + 1 : ℕ) = bktF A j a b c := by
  unfold bktF
  by_cases p1 : a <;> by_cases p2 : b <;> by_cases p3 : c <;> simp [p1, p2, p3]

section body

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
open Classical in
/-- **One arc of the bucket loop.** -/
theorem bktBody_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool} {N : NF}
    {x : WPos} {AB j : ℕ} (hj : j < N.arcs.length) (hx : GoodPos (Qof P) x)
    (hs : GoodPos (Qof P) (N.arc j).s) (he : GoodPos (Qof P) (N.arc j).e)
    (h14 : d.nmem (d.nreg 217114) = j)
    (m1 : d.nmem (AB + 5 * j + 1) = (N.arc j).s.edge) (m2 : d.nmem (AB + 5 * j + 2) = (N.arc j).s.hgt)
    (m3 : d.nmem (AB + 5 * j + 3) = (N.arc j).e.edge) (m4 : d.nmem (AB + 5 * j + 4) = (N.arc j).e.hgt)
    (hAW : AB + 5 * j + 4 ≤ W) (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h13W : d.nreg 217113 + 1 ≤ W) (h14W : d.nreg 217114 + 1 ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h44 : d.nreg 217044 = 2)
    (h10 : d.nreg 217110 = x.edge) (h11 : d.nreg 217111 = x.hgt) :
    ∃ d' k, Exec P W bktBody d d' k ∧ k ≤ 300 ∧
      d'.nreg 217113 = d.nreg 217113 + 1 ∧ d'.nreg 217114 = d.nreg 217114 + 1 ∧
      d'.nreg 217115 = (if d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x then 1 else d.nreg 217115) ∧
      d'.nreg 217112 = (if d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x then
        bktF N.arcs.length j (PosEq x (N.arc j).s) (PosEq x (N.arc j).e)
          (PosLt (Qof P) li (N.arc j).s x) else d.nreg 217112) ∧
      FrameB Bbkt d d' := by
  have hW1 : 1 ≤ W := by omega
  
  -- read the arc
  obtain ⟨d1, k1, e1, hk1, a16, a18, a19, a20, a21, f1⟩ := arcRd_exec (P := P) d hw h14 h27 h31 hAW
    m1 m2 m3 m4
  have hw1 := e1.wb_right
  have g1 := f1.1
  -- `eqS`, `eqE`
  obtain ⟨d2, k2, e2, hk2, n2⟩ := (ram_app% (eq2S_exec (P := P) d1 hw1 (a := 217110) (b := 217118)
    (c := 217111) (e := 217119) (dst := 217122) ?_ ?_ ?_ ?_ hW1))
  have hw2 := e2.wb_right
  obtain ⟨d3, k3, e3, hk3, n3⟩ := (ram_app% (eq2S_exec (P := P) d2 hw2 (a := 217110) (b := 217120)
    (c := 217111) (e := 217121) (dst := 217123) ?_ ?_ ?_ ?_ hW1))
  have hw3 := e3.wb_right
  -- values in `d3`
  have c10 : d3.nreg 217110 = x.edge := by
    ram_finish [n3.other, n2.other, g1, h10]
  have c11 : d3.nreg 217111 = x.hgt := by
    ram_finish [n3.other, n2.other, g1, h11]
  have c18 : d3.nreg 217118 = (N.arc j).s.edge := by
    ram_finish [n3.other, n2.other, a18]
  have c19 : d3.nreg 217119 = (N.arc j).s.hgt := by
    ram_finish [n3.other, n2.other, a19]
  have c20 : d3.nreg 217120 = (N.arc j).e.edge := by
    ram_finish [n3.other, n2.other, a20]
  have c21 : d3.nreg 217121 = (N.arc j).e.hgt := by
    ram_finish [n3.other, n2.other, a21]
  have q3 : ∀ r, Bbkt r = false → d3.nreg r = d.nreg r := fun r hr => by
    rw [n3.other (by simp only [Bbkt, decide_eq_false_iff_not] at hr; omega),
      n2.other (by simp only [Bbkt, decide_eq_false_iff_not] at hr; omega),
      g1 r (by simp only [Bbkt, Brd, decide_eq_false_iff_not] at hr ⊢; omega)]
  have b22 : d3.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    ram_rw [n3.other, n2.same, g1 217110, g1 217111, h10, h11, a18,
      a19]
    rfl
  have b23 : d3.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    ram_rw [n3.same, n2.other, n2.other, n2.other,
      n2.other, g1 217110, g1 217111, h10, h11, a20, a21]
    rfl
  -- the three comparisons
  have hsx := posLtF_iff hG li hs.2.2 hs.2.1 hs.1.2.2 hx.2.1 hx.1.2.2
  have hse := posLtF_iff hG li hs.2.2 hs.2.1 hs.1.2.2 he.2.1 he.1.2.2
  have hxe := posLtF_iff hG li hx.2.2 hx.2.1 hx.1.2.2 he.2.1 he.1.2.2
  obtain ⟨d4, k4, e4, hk4, v4⟩ := posLtOn_exec (P := P) d3 hw3 (a := 217118) (b := 217119)
    (c := 217120) (e := 217121) (dst := 217124) (n := (Qof P).n) (li := li)
    (by ram_rw [q3, h20]) (by ram_rw [q3, h26]) (by ram_rw [q3, h27])
    (by rw [c18]; exact hs.2.2) hnW hW1 (by decide) (by decide) (by decide) (by decide)
  have f4 : FrameB (Bon 217124) d3 d4 := exec_frameB e4 (by decide)
  have hw4 := e4.wb_right
  obtain ⟨d5, k5, e5, hk5, v5⟩ := posLtOn_exec (P := P) d4 hw4 (a := 217118) (b := 217119)
    (c := 217110) (e := 217111) (dst := 217125) (n := (Qof P).n) (li := li)
    (by ram_finish [f4.1, q3, h20])
    (by ram_finish [f4.1, q3, h26])
    (by ram_finish [f4.1, q3, h27])
    (by ram_rw [f4.1, c18]; exact hs.2.2) hnW hW1 (by decide) (by decide) (by decide)
    (by decide)
  have f5 : FrameB (Bon 217125) d4 d5 := exec_frameB e5 (by decide)
  have hw5 := e5.wb_right
  obtain ⟨d6, k6, e6, hk6, v6⟩ := posLtOn_exec (P := P) d5 hw5 (a := 217110) (b := 217111)
    (c := 217120) (e := 217121) (dst := 217126) (n := (Qof P).n) (li := li)
    (by ram_finish [f5.1, f4.1, q3, h20])
    (by ram_finish [f5.1, f4.1, q3, h26])
    (by ram_finish [f5.1, f4.1, q3, h27])
    (by ram_rw [f5.1, f4.1, c10]; exact hx.2.2) hnW hW1 (by decide)
    (by decide) (by decide) (by decide)
  have f6 : FrameB (Bon 217126) d5 d6 := exec_frameB e6 (by decide)
  have hw6 := e6.wb_right
  have b24 : d6.nreg 217124 = if PosLt (Qof P) li (N.arc j).s (N.arc j).e then 1 else 0 := by
    ram_finish [f6.1, f5.1, v4, c18, c19, c20, c21, hse]
  have b25 : d6.nreg 217125 = if PosLt (Qof P) li (N.arc j).s x then 1 else 0 := by
    frame_finish
  have b26 : d6.nreg 217126 = if PosLt (Qof P) li x (N.arc j).e then 1 else 0 := by
    ram_simp [v6, f5.1, f4.1, c10, c11, c20, c21, hxe]
  have q6 : ∀ r, Bbkt r = false → d6.nreg r = d.nreg r := fun r hr => by
    have hr' : Bon 217124 r = false ∧ Bon 217125 r = false ∧ Bon 217126 r = false := by
      simp only [Bbkt, Bon, decide_eq_false_iff_not] at hr ⊢; omega
    rw [f6.1 _ hr'.2.2, f5.1 _ hr'.2.1, f4.1 _ hr'.1, q3 r hr]
  have b22' : d6.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    ram_simp [f6.1, f5.1, f4.1, b22]
  have b23' : d6.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    ram_simp [f6.1, f5.1, f4.1, b23]
  -- the arc test
  obtain ⟨d7, k7, e7, hk7, n7⟩ := onS_exec (P := P) d6 hw6 hW1 (by ram_rw [q6, h27])
  have hw7 := e7.wb_right
  have b27 : d7.nreg 217127 = if OnArcP (Qof P) li N j x then 1 else 0 := by
    rw [n7.same, b22', b23', b24, b25, b26]
    exact onArc_bits (Qof P) li N j x
  have q7 : ∀ r, Bbkt r = false → d7.nreg r = d.nreg r := fun r hr => by
    rw [n7.other (by simp only [Bbkt, decide_eq_false_iff_not] at hr; omega), q6 r hr]
  -- the bucket
  have j16 : d7.nreg 217116 = j := by
    ram_simp [n7.other, f6.1, f5.1, f4.1, n3.other, n2.other, a16]
  have p15 : d7.nreg 217115 = d.nreg 217115 := by
    ram_simp [n7.other, f6.1, f5.1, f4.1, n3.other, n2.other, g1]
  have p12 : d7.nreg 217112 = d.nreg 217112 := by
    ram_simp [n7.other, f6.1, f5.1, f4.1, n3.other, n2.other, g1]
  have b22'' : d7.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    simp [n7.other, b22']
  have b23'' : d7.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    simp [n7.other, b23']
  have b25'' : d7.nreg 217125 = if PosLt (Qof P) li (N.arc j).s x then 1 else 0 := by
    simp [n7.other, b25]
  obtain ⟨d8, k8, e8, hk8, v15, v12, f8⟩ : ∃ d8 k8, Exec P W (.ifLtN 217115 217027
      (.ifLtN 217127 217027 .skip (.seq bktFS (block [.constN 217115 1]))) .skip) d7 d8 k8 ∧
      k8 ≤ 20 ∧
      d8.nreg 217115 = (if d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x then 1
        else d.nreg 217115) ∧
      d8.nreg 217112 = (if d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x then
        bktF N.arcs.length j (PosEq x (N.arc j).s) (PosEq x (N.arc j).e)
          (PosLt (Qof P) li (N.arc j).s x) else d.nreg 217112) ∧
      FrameB (fun r => decide (r = 217112 ∨ r = 217115 ∨ r = 217128)) d7 d8 := by
    have c27 := (q7 217027 (by decide)).trans h27
    by_cases c1 : d.nreg 217115 < 1
    · by_cases c2 : OnArcP (Qof P) li N j x
      · obtain ⟨d8, k8, e8, hk8, w12, f8⟩ := bktFS_exec (P := P) d7 hw7 hj h2A c27
          (by ram_rw [q7, h30]) (by ram_rw [q7, h44]) j16
        obtain ⟨d9, k9, e9, hk9, n9⟩ := x_const (P := P) d8 e8.wb_right 217115 1 hW1
        have ex : Exec P W (.ifLtN 217115 217027
            (.ifLtN 217127 217027 .skip (.seq bktFS (block [.constN 217115 1]))) .skip) d7 d9
            (k8 + k9 + 2 + 1) :=
          .ifLtN_true (by rwa [p15, c27])
            (.ifLtN_false (by rw [b27, c27, ite_eq_left c2]; omega) (.seq e8 e9))
        refine ⟨d9, _, ex, by omega, ?_, ?_, ?_⟩
        · rw [n9.same, ite_eq_left ⟨c1, c2⟩]
        · ram_rw [n9.other, w12, b22'', b23'', b25'',
            ite_eq_left (show d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x from ⟨c1, c2⟩)]
          exact bktF_bits _ _ _ _ _
        · ram_frame
      · have ex : Exec P W (.ifLtN 217115 217027
            (.ifLtN 217127 217027 .skip (.seq bktFS (block [.constN 217115 1]))) .skip) d7 d7
            (0 + 1 + 1) :=
          .ifLtN_true (by rwa [p15, c27])
            (by ram_path)
        refine ⟨d7, _, ex, by omega, ?_, ?_, FrameB.refl _ _⟩
        · rw [p15, ite_eq_right (show ¬ (d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x) from
            fun h => c2 h.2)]
        · rw [p12, ite_eq_right (show ¬ (d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x) from
            fun h => c2 h.2)]
    · have ex : Exec P W (.ifLtN 217115 217027
          (.ifLtN 217127 217027 .skip (.seq bktFS (block [.constN 217115 1]))) .skip) d7 d7
          (0 + 2) := .ifLtN_false (by rwa [p15, c27]) (.skip hw7)
      refine ⟨d7, _, ex, by omega, ?_, ?_, FrameB.refl _ _⟩
      · rw [p15, ite_eq_right (show ¬ (d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x) from
          fun h => c1 h.1)]
      · rw [p12, ite_eq_right (show ¬ (d.nreg 217115 < 1 ∧ OnArcP (Qof P) li N j x) from
          fun h => c1 h.1)]
  have hw8 := e8.wb_right
  -- advance
  have p13 : d8.nreg 217113 = d.nreg 217113 := by
    ram_simp [f8.1, n7.other, f6.1, f5.1, f4.1, n3.other, n2.other, g1]
  have p14 : d8.nreg 217114 = d.nreg 217114 := by
    ram_simp [f8.1, n7.other, f6.1, f5.1, f4.1, n3.other, n2.other, g1]
  have p27 : d8.nreg 217027 = 1 := by ram_simp [f8.1, q7, h27]
  obtain ⟨d9, k9, e9, hk9, w13, w14, g9⟩ : ∃ d9 k9, Exec P W (block [.addN 217114 217114 217027,
      .addN 217113 217113 217027]) d8 d9 k9 ∧ k9 ≤ 2 ∧ d9.nreg 217113 = d.nreg 217113 + 1 ∧
      d9.nreg 217114 = d.nreg 217114 + 1 ∧
      (∀ r, r ≠ 217113 → r ≠ 217114 → d9.nreg r = d8.nreg r) := by
    exec_block!
    · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;> config_simp
      · omega
      · omega
      · ram_simp []
  have ex : Exec P W bktBody d d9 (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + k9)))))))) := by
    ram_path
  exact ⟨d9, _, ex, by omega, w13, w14, by simp [g9, v15],
    by simp [g9, v12], exec_frameB ex wr_bktBody⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`bktS`: the bucket of the position `⟨217110, 217111⟩`** (it lies on the closure of an arc
of the region). -/
theorem bktS_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool} {N : NF}
    {x : WPos} {AB RA nRA : ℕ} {ras : ℕ → ℕ} (hx : GoodPos (Qof P) x)
    (hgood : ∀ j, j < N.arcs.length → GoodPos (Qof P) (N.arc j).s ∧ GoodPos (Qof P) (N.arc j).e)
    (hAm : ∀ j, j < N.arcs.length → d.nmem (AB + 5 * j + 1) = (N.arc j).s.edge ∧
      d.nmem (AB + 5 * j + 2) = (N.arc j).s.hgt ∧ d.nmem (AB + 5 * j + 3) = (N.arc j).e.edge ∧
      d.nmem (AB + 5 * j + 4) = (N.arc j).e.hgt)
    (hRm : ∀ t, t < nRA → d.nmem (RA + t) = ras t ∧ ras t < N.arcs.length)
    (hAW : ∀ j, j < N.arcs.length → AB + 5 * j + 4 ≤ W) (hRW : RA + nRA ≤ W)
    (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h32 : d.nreg 217032 = nRA)
    (h33 : d.nreg 217033 = RA) (h44 : d.nreg 217044 = 2)
    (h10 : d.nreg 217110 = x.edge) (h11 : d.nreg 217111 = x.hgt)
    (hex : ∃ t, t < nRA ∧ OnArcP (Qof P) li N (ras t) x) :
    ∃ d' k, Exec P W bktS d d' k ∧ k ≤ 302 * nRA + 6 ∧
      (∃ t, t < nRA ∧ OnArcP (Qof P) li N (ras t) x ∧
        d'.nreg 217112 = bktF N.arcs.length (ras t) (PosEq x (N.arc (ras t)).s)
          (PosEq x (N.arc (ras t)).e) (PosLt (Qof P) li (N.arc (ras t)).s x)) ∧
      FrameB Bbkt d d' := by
  obtain ⟨d0, k0, e0, hk0, a13, a14, a15, f0⟩ : ∃ d0 k0, Exec P W (block [.constN 217113 0,
      .copyN 217114 217033, .constN 217115 0, .constN 217112 0]) d d0 k0 ∧ k0 ≤ 4 ∧
      d0.nreg 217113 = 0 ∧ d0.nreg 217114 = RA ∧ d0.nreg 217115 = 0 ∧ FrameB Bbkt d d0 := by
    obtain ⟨d0, k0, e0, hk0, a13, a14, a15⟩ : ∃ d0 k0, Exec P W (block [.constN 217113 0,
        .copyN 217114 217033, .constN 217115 0, .constN 217112 0]) d d0 k0 ∧ k0 ≤ 4 ∧
        d0.nreg 217113 = 0 ∧ d0.nreg 217114 = RA ∧ d0.nreg 217115 = 0 := by
      exec_block!
      simp_all
    exact ⟨d0, k0, e0, hk0, a13, a14, a15, exec_frameB e0 (by decide)⟩
  let Inv := fun t c => WordsBounded W c ∧ c.nreg 217113 = t ∧
    c.nreg 217032 = nRA ∧ c.nreg 217114 = RA + t ∧ c.nreg 217115 ≤ 1 ∧
    (c.nreg 217115 = 1 → ∃ t', t' < t ∧ OnArcP (Qof P) li N (ras t') x ∧
      c.nreg 217112 = bktF N.arcs.length (ras t') (PosEq x (N.arc (ras t')).s)
        (PosEq x (N.arc (ras t')).e) (PosLt (Qof P) li (N.arc (ras t')).s x)) ∧
    (c.nreg 217115 = 0 → ∀ t', t' < t → ¬ OnArcP (Qof P) li N (ras t') x) ∧ FrameB Bbkt d c
  obtain ⟨d', k', e', ⟨-, -, -, -, h15, hfound, hnot, f'⟩, hk'⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 217113) (nr := 217032) (body := bktBody) Inv 300 nRA
    (fun t c hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩)
    (fun t c ht hc => by
      obtain ⟨hwc, c13, c32, c14, c15, cfound, cnot, cf⟩ := hc
      have g := cf.1
      have cm := cf.2.2.1
      obtain ⟨hR1, hR2⟩ := hRm t ht
      obtain ⟨hgs, hge⟩ := hgood _ hR2
      obtain ⟨m1, m2, m3, m4⟩ := hAm _ hR2
      obtain ⟨c', kb, eb, hkb, b13, b14, b15, b12, bf⟩ := bktBody_exec (P := P) c hwc hG (li := li)
        (N := N) (x := x) (AB := AB) hR2 hx hgs hge (by rwa [c14, cm])
        (by rwa [cm]) (by rwa [cm]) (by rwa [cm])
        (by rwa [cm]) (hAW _ hR2) h2A hnW (by omega) (by omega)
        (by ram_rw [g, h20]) (by ram_rw [g, h26])
        (by ram_rw [g, h27]) (by ram_rw [g, h30])
        (by ram_rw [g, h31]) (by ram_rw [g, h44])
        (by ram_rw [g, h10]) (by ram_rw [g, h11])
      refine ⟨c', kb, eb, ⟨eb.wb_right, by omega, by ram_rw [bf.1, c32], by omega, ?_,
        ?_, ?_, cf.trans bf⟩, hkb⟩
      · rw [b15]; split_ifs <;> omega
      · intro h1
        by_cases hc : c.nreg 217115 < 1 ∧ OnArcP (Qof P) li N (ras t) x
        · exact ⟨t, by omega, hc.2, by rw [b12, ite_eq_left hc]⟩
        · rw [b15, ite_eq_right hc] at h1
          obtain ⟨t', ht', hon, hv⟩ := cfound h1
          exact ⟨t', by omega, hon, by rw [b12, ite_eq_right hc, hv]⟩
      · intro h0 t' ht'
        by_cases hc : c.nreg 217115 < 1 ∧ OnArcP (Qof P) li N (ras t) x
        · simp_all 
        · rw [b15, ite_eq_right hc] at h0
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | h
          · exact cnot h0 t' h
          · subst h; exact fun hon => hc ⟨by omega, hon⟩)
    (j := 0) ⟨e0.wb_right, a13, by ram_rw [f0.1, h32], by omega, by omega,
      fun h => by omega, fun _ t' ht' => absurd ht' (Nat.not_lt_zero _), f0⟩ (Nat.zero_le _)
  have hk : k0 + k' ≤ 302 * nRA + 6 := by
    have : nRA - 0 = nRA := Nat.sub_zero _
    rw [this] at hk'; omega
  refine ⟨d', k0 + k', .seq e0 e', hk, ?_, f'⟩
  obtain ⟨t, ht, hon⟩ := hex
  by_cases h0 : d'.nreg 217115 = 0
  · exact absurd hon (hnot h0 t ht)
  · exact hfound (by omega)

end body

end

end DrvX

end Chazelle.Core
