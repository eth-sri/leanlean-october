module

public import Chazelle.Core.DownPhaseDrvXRamB
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 4000000

/-!
# Down phase, extraction (D6), RAM part 3: classifying a chord end, its interior edge

* `clsS_exec`: for the end at walk edge `p` of a chord at height `h`, the regular-inner bit
  `[RegIn …]` and the symbolic host point at the start of walk edge `p`;
* `peS_exec`: the interior walk edge `pEdge li n s` of an encoded host point `s`.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)

@[expose] public section

theorem NRegs.same {d d' : Config} {r v : ℕ} (h : NRegs d d' (upd d.nreg r v)) : d'.nreg r = v := by
  rw [h.1, Machine.upd_same]

theorem NRegs.other {d d' : Config} {r v : ℕ} (h : NRegs d d' (upd d.nreg r v)) {r' : ℕ}
    (hr : r' ≠ r) : d'.nreg r' = d.nreg r' := by
  rw [h.1, Machine.upd_other _ _ _ hr]

theorem seqs_one (s : Stmt) : seqs [s] = s := rfl

theorem tS_le {m T : ℕ} (β : Bool) (hT : T ≤ m) : tS m T β ≤ 2 * m := by
  unfold tS; splao

theorem red_red {x M : ℕ} (_hM : 0 < M) (hx : x < 3 * M) :
    (if (if x < M then x else x - M) < M then (if x < M then x else x - M)
      else (if x < M then x else x - M) - M) = x % M := by
  by_cases h1 : x < M
  · rw [ite_eq_left h1, ite_eq_left h1, Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right h1]
    by_cases h2 : x - M < M
    · rw [ite_eq_left h2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
    · rw [ite_eq_right h2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]

/-- The registers `clsS` writes. -/
def Bcls (r : ℕ) : Bool :=
  decide ((217061 ≤ r ∧ r ≤ 217067) ∨ r = 217070 ∨ r = 217071 ∨ r = 217072 ∨
    (217090 ≤ r ∧ r ≤ 217097))

theorem Blook_cls {r : ℕ} (h : Bcls r = false) : Blook r = false := by
  sio only [Bcls, Blook, decide_eq_false_iff_not] at h ⊢

section cls

variable {P : Polygon} {W : ℕ}

/-- **`clsS`: the end at walk edge `p = 217060`** of the chord at height `h = 217050`. -/
theorem clsS_exec (d : Config) (hw : WordsBounded W d) {n m T HB h p : ℕ} {β li : Bool}
    {H : Host} (hH : HostAt d.nmem HB H) (hwf : HostWF n H) (hlen : H.length ≤ 64)
    (hHB : HB + 3 * H.length + 1 ≤ W) (hW : 256 * n + 16 ≤ W)
    (hm1 : 1 ≤ m) (hmp : m + 1 = (H.pts n).length) (hT : T ≤ m) (hp : p ≤ 2 * m + 6)
    (h20 : d.nreg 217020 = n) (h21 : d.nreg 217021 = m) (h22 : d.nreg 217022 = 2 * m)
    (h25 : d.nreg 217025 = tS m T β) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h34 : d.nreg 217034 = H.length) (h35 : d.nreg 217035 = HB + 1) (h41 : d.nreg 217041 = 6)
    (h42 : d.nreg 217042 = 2 * m + 6) (h44 : d.nreg 217044 = 2) (h50 : d.nreg 217050 = h)
    (h60 : d.nreg 217060 = p) :
    ∃ d' k, Exec P W clsS d d' k ∧ k ≤ 2200 ∧
      d'.nreg 217064 = (if RegIn n H li m T β h p then 1 else 0) ∧
      Enc d' (hpt n H (tK m T β p)) ∧ FrameB Bcls d d' := by
  have hptsW : (H.pts n).length ≤ 64 * n :=
    (Host.pts_length_le hwf).trans (Nat.mul_le_mul_right _ hlen)
  have hmW : 4 * m + 6 ≤ W := by omega
  have htS := tS_le (m := m) (T := T) β hT
  -- `u := tS + (p - 6)`
  obtain ⟨d1, k1, e1, hk1, n1⟩ : ∃ d1 k1, Exec P W (block [.subN 217061 217060 217041,
      .addN 217061 217025 217061]) d d1 k1 ∧ k1 ≤ 2 ∧
      NRegs d d1 (upd d.nreg 217061 (tS m T β + (p - 6))) := by
    exec_block
    · config_simp; rwo [h25, h60, h41]
    · refine ⟨by omega, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [h25, h60, h41]
  have hw1 := e1.wb_right
  have f1 : FrameB Bcls d d1 := exec_frameB e1 (by decide)
  -- reduce twice
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217022)
    (r := 217061) (t := .skip) (e := block [.subN 217061 217061 217022]) (d := d1) (K := 1)
    (fun _ => x_skipR d1 hw1 217061) (fun _ => x_sub d1 hw1 217061 217061 217022)
  have hw2 := e2.wb_right
  have f2 : FrameB Bcls d d2 := f1.trans (exec_frameB e2 (by decide))
  obtain ⟨d3, k3, e3, hk3, n3⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217022)
    (r := 217061) (t := .skip) (e := block [.subN 217061 217061 217022]) (d := d2) (K := 1)
    (fun _ => x_skipR d2 hw2 217061) (fun _ => x_sub d2 hw2 217061 217061 217022)
  have hw3 := e3.wb_right
  have f3 : FrameB Bcls d d3 := f2.trans (exec_frameB e3 (by decide))
  have g22 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217022 = 2 * m := fun hc =>
    (hc.1 _ (by decide)).trans h22
  have v3 : d3.nreg 217061 = tU m T β p := by
    rw [n3.same, n2.same, n2.other (by decide), n1.same, g22 f1]
    exact red_red (by omega) (by omega)
  -- side bit
  obtain ⟨d4, k4, e4, hk4, n4⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217021)
    (r := 217063) (t := block [.constN 217063 1]) (e := block [.constN 217063 0]) (d := d3)
    (K := 1) (fun _ => x_const d3 hw3 217063 1 (by omega))
    (fun _ => x_const d3 hw3 217063 0 (by omega))
  have hw4 := e4.wb_right
  have f4 : FrameB Bcls d d4 := f3.trans (exec_frameB e4 (by decide))
  have g21 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217021 = m := fun hc =>
    (hc.1 _ (by decide)).trans h21
  have v4 : d4.nreg 217063 = if tU m T β p < m then 1 else 0 := by
    rw [n4.same, v3, g21 f3]
  -- `kc := sideE m u`
  obtain ⟨d5, k5, e5, hk5, n5⟩ := x_ifR (P := P) (W := W) (a := 217021) (b := 217061)
    (r := 217062) (t := block [.subN 217062 217022 217061]) (e := block [.copyN 217062 217061])
    (d := d4) (K := 1) (fun _ => x_sub d4 hw4 217062 217022 217061)
    (fun _ => x_copy d4 hw4 217062 217061)
  have hw5 := e5.wb_right
  have f5 : FrameB Bcls d d5 := f4.trans (exec_frameB e5 (by decide))
  have u4 : d4.nreg 217061 = tU m T β p := by rw [n4.other (by decide), v3]
  have v5 : d5.nreg 217062 = tK m T β p := by
    rw [n5.same, u4, g21 f4, g22 f4]
    unfold tK Chazelle.Chain.sideE
    have := tU_lt (T := T) β hm1 p
    splao
  -- lookup
  obtain ⟨d6, k6, e6, hk6, n6⟩ := x_copy (P := P) d5 hw5 217090 217062
  have hw6 := e6.wb_right
  have f6 : FrameB Bcls d d6 := f5.trans (exec_frameB e6 (by decide))
  have m6  := f6.2.2.1
  obtain ⟨d7, k7, e7, hk7, enc7, f7'⟩ := lookS_exec (P := P) d6 hw6 (by rwx [m6]) hwf hlen
    hHB (by omega) (by omega) ((f6.1 _ (by decide)).trans h20)
    ((f6.1 _ (by decide)).trans h27) ((f6.1 _ (by decide)).trans h34)
    ((f6.1 _ (by decide)).trans h35)
  have hw7 := e7.wb_right
  have f7 : FrameB Bcls d d7 := f6.trans ⟨fun r hr => f7'.1 r (Blook_cls hr),
    fun r hr => f7'.2.1 r (Blook_cls hr), f7'.2.2⟩
  have v6 : d6.nreg 217090 = tK m T β p := by rw [n6.same, v5]
  rw [v6] at enc7
  have enc7' := enc7 (by have := tK_le (T := T) β hm1 p; omega)
  -- height vertex
  obtain ⟨d8, k8, e8, hk8, n8⟩ := x_ifR (P := P) (W := W) (a := 217070) (b := 217044)
    (r := 217066) (t := block [.copyN 217066 217071]) (e := block [.copyN 217066 217072]) (d := d7)
    (K := 1) (fun _ => x_copy d7 hw7 217066 217071) (fun _ => x_copy d7 hw7 217066 217072)
  have hw8 := e8.wb_right
  have f8 : FrameB Bcls d d8 := f7.trans (exec_frameB e8 (by decide))
  have v8 : d8.nreg 217066 = hidx (hpt n H (tK m T β p)) := by
    rw [n8.same, (f7.1 _ (by decide)).trans h44]
    revert enc7'
    cases hpt n H (tK m T β p) with
    | vtx j => intro he; simp [Enc] at he; rwr [he.1, he.2, ite_eq_left (by omega)]
    | onEdge e h' => intro he; simp [Enc] at he; rwr [he.1, he.2.2, ite_eq_right (by omega)]
  -- `t0 := [h = hid]`
  obtain ⟨d9, k9, e9, hk9, n9⟩ := x_ifR (P := P) (W := W) (a := 217050) (b := 217066)
    (r := 217065) (t := block [.constN 217065 0])
    (e := .ifLtN 217066 217050 (block [.constN 217065 0]) (block [.constN 217065 1])) (d := d8)
    (K := 3) (fun _ => x_mono (x_const d8 hw8 217065 0 (by omega)) (by omega))
    (fun _ => x_ifR (fun _ => x_const d8 hw8 217065 0 (by omega))
      (fun _ => x_const d8 hw8 217065 1 (by omega)))
  have hw9 := e9.wb_right
  have f9 : FrameB Bcls d d9 := f8.trans (exec_frameB e9 (by decide))
  have v9 : d9.nreg 217065 =
      if tZ n H m T β h p then 1 else 0 := by
    rw [n9.same, v8, (f8.1 _ (by decide)).trans h50]
    unfold tZ
    splao
  -- the regular-inner bit
  obtain ⟨d10, k10, e10, hk10, n10⟩ := x_const (P := P) d9 hw9 217064 1 (by omega)
  have hw10 := e10.wb_right
  obtain ⟨d11, k11, e11, hk11, n11⟩ := x_ifR (P := P) (W := W) (a := 217060) (b := 217041)
    (r := 217064) (t := block [.constN 217064 0]) (e := .skip) (d := d10) (K := 1)
    (fun _ => x_const d10 hw10 217064 0 (by omega)) (fun _ => x_skipR d10 hw10 217064)
  have hw11 := e11.wb_right
  obtain ⟨d12, k12, e12, hk12, n12⟩ := x_ifR (P := P) (W := W) (a := 217042) (b := 217060)
    (r := 217064) (t := block [.constN 217064 0]) (e := .skip) (d := d11) (K := 1)
    (fun _ => x_const d11 hw11 217064 0 (by omega)) (fun _ => x_skipR d11 hw11 217064)
  have hw12 := e12.wb_right
  obtain ⟨d13, k13, e13, hk13, n13⟩ := x_ifR (P := P) (W := W) (a := 217060) (b := 217042)
    (r := 217064) (t := .skip)
    (e := .ifLtN 217042 217060 .skip
      (.ifLtN 217065 217027 (block [.constN 217064 0]) .skip)) (d := d12) (K := 5)
    (fun _ => x_mono (x_skipR d12 hw12 217064) (by omega))
    (fun _ => x_ifR (fun _ => x_mono (x_skipR d12 hw12 217064) (by omega))
      (fun _ => x_ifR (fun _ => x_const d12 hw12 217064 0 (by omega))
        (fun _ => x_skipR d12 hw12 217064)))
  have hw13 := e13.wb_right
  obtain ⟨d14, k14, e14, hk14, n14⟩ := x_ifR (P := P) (W := W) (a := 217065) (b := 217027)
    (r := 217064) (t := .skip)
    (e := .ifLtN 217062 217027 (block [.constN 217064 0])
      (.ifLtN 217062 217021 .skip (.ifLtN 217021 217062 .skip (block [.constN 217064 0]))))
    (d := d13) (K := 7)
    (fun _ => x_mono (x_skipR d13 hw13 217064) (by omega))
    (fun _ => x_ifR (fun _ => x_mono (x_const d13 hw13 217064 0 (by omega)) (by omega))
      (fun _ => x_ifR (fun _ => x_mono (x_skipR d13 hw13 217064) (by omega))
        (fun _ => x_ifR (fun _ => x_skipR d13 hw13 217064)
          (fun _ => x_const d13 hw13 217064 0 (by omega)))))
  have hw14 := e14.wb_right
  obtain ⟨d15, k15, e15, hk15, n15⟩ := x_ifR (P := P) (W := W) (a := 217063) (b := 217026)
    (r := 217064) (t := block [.constN 217064 0])
    (e := .ifLtN 217026 217063 (block [.constN 217064 0]) .skip) (d := d14) (K := 3)
    (fun _ => x_mono (x_const d14 hw14 217064 0 (by omega)) (by omega))
    (fun _ => x_ifR (fun _ => x_const d14 hw14 217064 0 (by omega))
      (fun _ => x_skipR d14 hw14 217064))
  -- frames of the last steps
  have f10 : FrameB Bcls d d10 := f9.trans (exec_frameB e10 (by decide))
  have f11 : FrameB Bcls d d11 := f10.trans (exec_frameB e11 (by decide))
  have f12 : FrameB Bcls d d12 := f11.trans (exec_frameB e12 (by decide))
  have f13 : FrameB Bcls d d13 := f12.trans (exec_frameB e13 (by decide))
  have f14 : FrameB Bcls d d14 := f13.trans (exec_frameB e14 (by decide))
  have f15 : FrameB Bcls d d15 := f14.trans (exec_frameB e15 (by decide))
  -- the inputs of the bit
  have q60 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217060 = p := fun hc =>
    (hc.1 _ (by decide)).trans h60
  have q41 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217041 = 6 := fun hc =>
    (hc.1 _ (by decide)).trans h41
  have q42 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217042 = 2 * m + 6 := fun hc =>
    (hc.1 _ (by decide)).trans h42
  have q27 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217027 = 1 := fun hc =>
    (hc.1 _ (by decide)).trans h27
  have q26 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217026 = liV li := fun hc =>
    (hc.1 _ (by decide)).trans h26
  obtain ⟨zb, hzb⟩ : ∃ zb : ℕ, zb = if tZ n H m T β h p then 1 else 0 := ⟨_, rfl⟩
  have hz1 : zb ≤ 1 := by rw [hzb]; splao
  have hzt : tZ n H m T β h p ↔ zb = 1 := by
    rw [hzb]; constructor
    · intro hz; rw [ite_eq_left hz]
    · intro hz; by_contra hz'; rwo [ite_eq_right hz'] at hz
  have t65 : d12.nreg 217065 = zb := by
    rw [n12.other (by decide), n11.other (by decide), n10.other (by decide), v9, hzb]
  have t65' : d13.nreg 217065 = zb := by
    rw [n13.other (by decide), t65]
  have t62 : d13.nreg 217062 = tK m T β p := by
    rw [n13.other (by decide), n12.other (by decide), n11.other (by decide),
      n10.other (by decide), n9.other (by decide), n8.other (by decide),
      f7'.1 _ (by decide), n6.other (by decide), v5]
  have t63 : d14.nreg 217063 = if tU m T β p < m then 1 else 0 := by
    rw [n14.other (by decide), n13.other (by decide), n12.other (by decide),
      n11.other (by decide), n10.other (by decide), n9.other (by decide), n8.other (by decide),
      f7'.1 _ (by decide), n6.other (by decide), n5.other (by decide), v4]
  have w11 : d11.nreg 217064 = if 6 ≤ p then 1 else 0 := by
    rw [n11.same, q60 f10, q41 f10, n10.same]
    splao
  have w12 : d12.nreg 217064 = if 6 ≤ p then 1 else 0 := by
    rw [n12.same, q60 f11, q42 f11, w11, ite_eq_right (show ¬ (2 * m + 6 < p) by omega)]
  have w13 : d13.nreg 217064 = if 6 ≤ p ∧ (p = 2 * m + 6 → zb = 1) then 1 else 0 := by
    rw [n13.same, q60 f12, q42 f12, w12, t65, q27 f12]
    splao
  have w14 : d14.nreg 217064 =
      if 6 ≤ p ∧ (p = 2 * m + 6 → zb = 1) ∧
        ¬ (zb = 1 ∧ (tK m T β p = 0 ∨ tK m T β p = m)) then 1 else 0 := by
    rw [n14.same, t65', q27 f13, t62, (f13.1 _ (by decide)).trans h21, w13]
    splao
  have w15' : d15.nreg 217064 =
      if (6 ≤ p ∧ (p = 2 * m + 6 → zb = 1) ∧
        ¬ (zb = 1 ∧ (tK m T β p = 0 ∨ tK m T β p = m))) ∧
          (tU m T β p < m ↔ liV li = 1) then 1 else 0 := by
    rw [n15.same, t63, q26 f14, w14]
    have := liV_le li
    splao
  have hreg : ((6 ≤ p ∧ (p = 2 * m + 6 → zb = 1) ∧
      ¬ (zb = 1 ∧ (tK m T β p = 0 ∨ tK m T β p = m))) ∧ (tU m T β p < m ↔ liV li = 1)) ↔
        RegIn n H li m T β h p := by
    unfold RegIn
    have hl : liV li = 1 ↔ li = true := by cases li <;> simp [liV]
    rw [hl, ← hzt]
    constructor
    · rintro ⟨⟨h6, hlast, hirr⟩, hside⟩; exact ⟨h6, hp, hlast, hirr, hside⟩
    · rintro ⟨h6, -, hlast, hirr, hside⟩; exact ⟨⟨h6, hlast, hirr⟩, hside⟩
  have w15 : d15.nreg 217064 = if RegIn n H li m T β h p then 1 else 0 := by
    rw [w15']; exact if_congr hreg rfl rfl
  simp [clsS, seqs_cons₂, seqs_one]
  refine ⟨d15, _, .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9
      (.seq e10 (.seq e11 (.seq e12 (.seq e13 (.seq e14 e15))))))))))))), by omega, w15, ?_, f15⟩
  · have k70 : d15.nreg 217070 = d7.nreg 217070 := by
      rw [n15.other (by decide), n14.other (by decide), n13.other (by decide),
        n12.other (by decide), n11.other (by decide), n10.other (by decide),
        n9.other (by decide), n8.other (by decide)]
    have k71 : d15.nreg 217071 = d7.nreg 217071 := by
      rw [n15.other (by decide), n14.other (by decide), n13.other (by decide),
        n12.other (by decide), n11.other (by decide), n10.other (by decide),
        n9.other (by decide), n8.other (by decide)]
    have k72 : d15.nreg 217072 = d7.nreg 217072 := by
      rw [n15.other (by decide), n14.other (by decide), n13.other (by decide),
        n12.other (by decide), n11.other (by decide), n10.other (by decide),
        n9.other (by decide), n8.other (by decide)]
    exact enc7'.congr k70 k71 k72

end cls

/-! ## The interior edge of a host point -/

/-- The registers `peS` writes. -/
def Bpe (r : ℕ) : Bool := decide (217100 ≤ r ∧ r ≤ 217104)

theorem wr_pe : wr Bpe peS = true := by decide

section pe

variable {P : Polygon} {W : ℕ}

/-- **`peS`**: `217100 := pEdge li n s` for the encoded host point `s`. -/
theorem peS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool} {s : SymPt}
    (hs : s.Lt n) (henc : Enc d s) (hnW : n ≤ W)
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h44 : d.nreg 217044 = 2) :
    ∃ d' k, Exec P W peS d d' k ∧ k ≤ 40 ∧ d'.nreg 217100 = pEdge li n s ∧ FrameB Bpe d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W peS d d' k ∧ k ≤ 40 ∧
      d'.nreg 217100 = pEdge li n s := by
    unfold peS
    cases s with
    | vtx j =>
      simp [Enc] at henc
      simp [SymPt.Lt] at hs
      refine spec_ifLtN_true (by rwo [henc.1, h44]) ?_
      obtain ⟨d1, k1, e1, hk1, n1, -⟩ := ivBS_exec (P := P) d hw (src := 217071) (dst := 217100)
        h20 h26 h27 (by decide) (by decide) (by decide)
      exact ⟨d1, k1, e1, by omega, by rwr [n1, Machine.upd_same, henc.2]⟩
    | onEdge e h =>
      simp [Enc] at henc
      simp [SymPt.Lt] at hs
      refine spec_ifLtN_false (by rwo [henc.1, h44]) ?_
      obtain ⟨d1, k1, e1, hk1, a1, o1, -, m1, -⟩ := qES_exec (P := P) d hw (src := 217071)
        (dst := 217101) h20 h26 h27 (by rw [henc.2.1]; exact hs.1) hnW (by decide) (by decide)
        (by decide) (by decide) (by decide)
      have hq  := DownMath.qE_lt li hs.1
      rw [henc.2.1] at a1
      obtain ⟨d2, k2, e2, hk2, n2, -⟩ := succS_exec (P := P) d1 e1.wb_right (src := 217101)
        (dst := 217102) (n := n) (by rw [o1 _ (by decide) (by decide), h20])
        (by rw [o1 _ (by decide) (by decide), h27]) (by rwx [a1]) hnW (by decide)
      have b2 : d2.nreg 217102 = (DrvR.qE li n e + 1) % n := by rw [n2, Machine.upd_same, a1]
      have o2 : ∀ r, r ≠ 217102 → d2.nreg r = d1.nreg r := fun r hr => by
        rw [n2, Machine.upd_other _ _ _ hr]
      obtain ⟨d3, k3, e3, hk3, n3, -⟩ := ivBS_exec (P := P) d2 e2.wb_right (src := 217102)
        (dst := 217103) (n := n) (li := li)
        (by rw [o2 _ (by decide), o1 _ (by decide) (by decide), h20])
        (by rw [o2 _ (by decide), o1 _ (by decide) (by decide), h26])
        (by rw [o2 _ (by decide), o1 _ (by decide) (by decide), h27])
        (by decide) (by decide) (by decide)
      have b3 : d3.nreg 217103 = DrvR.ivB li n ((DrvR.qE li n e + 1) % n) := by
        rw [n3, Machine.upd_same, b2]
      have o3 : ∀ r, r ≠ 217103 → d3.nreg r = d2.nreg r := fun r hr => by
        rw [n3, Machine.upd_other _ _ _ hr]
      have b72 : d3.nreg 217072 = h := by
        rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide) (by decide), henc.2.2]
      have b101 : d3.nreg 217101 = DrvR.qE li n e := by
        rw [o3 _ (by decide), o2 _ (by decide), a1]
      have b102 : d3.nreg 217102 = (DrvR.qE li n e + 1) % n := by rw [o3 _ (by decide), b2]
      have hw3 := e3.wb_right
      obtain ⟨d4, k4, e4, hk4, n4⟩ := x_ifR (P := P) (W := W) (a := 217072) (b := 217103)
        (r := 217100) (t := block [.copyN 217100 217101])
        (e := .ifLtN 217103 217072 (block [.copyN 217100 217101]) (block [.copyN 217100 217102]))
        (d := d3) (K := 3) (fun _ => x_mono (x_copy d3 hw3 217100 217101) (by omega))
        (fun _ => x_ifR (fun _ => x_copy d3 hw3 217100 217101)
          (fun _ => x_copy d3 hw3 217100 217102))
      refine ⟨d4, k1 + (k2 + (k3 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), by omega, ?_⟩
      rw [n4.same, b72, b3, b101, b102]
      simp [pEdge]
      splao
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_pe⟩

end pe

end

end DrvX

end Chazelle.Core
