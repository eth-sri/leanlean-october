module

public import Chazelle.Core.DownPhaseDrvXRamC

/-!
# Down phase, extraction (D6), RAM part 4: the bucket of a position

* `posLtF_iff`: `posLtS` decides the key order `PosLt` of two positions;
* `eq2S_exec`, `posLtOn_exec`, `onS_exec`, `bktFS_exec`, `arcRd_exec`: the pieces of `bktBody`;
* `bktS_exec`: the bucket loop over the arcs of the region finds an arc of the region on whose
  closure the position lies, and computes `bktF` for it.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)

@[expose] public section

theorem hltF_le (P : Polygon) (u v : ℕ) : hltF P u v ≤ 1 := by
  unfold hltF; split_ifs <;> omega

theorem hltF_eq_one {P : Polygon} (hG : GoodEnv P) {u v : ℕ} (hu : u < (Qof P).n)
    (hv : v < (Qof P).n) : hltF P u v = 1 ↔ ((Qof P).vtx u).2 < ((Qof P).vtx v).2 := by
  rw [hlt_iff hG hu hv]; unfold hltF; split_ifs with h <;> simp [h]

open Classical in
/-- **`posLtS` decides the key order** of two positions at vertex heights. -/
theorem posLtF_iff {P : Polygon} (hG : GoodEnv P) (li : Bool) {x y : WPos}
    (hx : x.edge < (Qof P).n) (hx1 : 1 ≤ x.hgt) (hxn : x.hgt ≤ (Qof P).n) (hy1 : 1 ≤ y.hgt)
    (hyn : y.hgt ≤ (Qof P).n) :
    posLtF P li (Qof P).n x.edge x.hgt y.edge y.hgt = if PosLt (Qof P) li x y then 1 else 0 := by
  have hn : 0 < (Qof P).n := by omega
  have h1 := hltF_eq_one hG (DownMath.ivB_lt li hx) (DownMath.ivB_lt li (Nat.mod_lt (x.edge + 1) hn))
  have h2 := hltF_eq_one hG (u := x.hgt - 1) (v := y.hgt - 1) (by omega) (by omega)
  have b1 := hltF_le P (ivB li (Qof P).n x.edge) (ivB li (Qof P).n ((x.edge + 1) % (Qof P).n))
  have b2 := hltF_le P (x.hgt - 1) (y.hgt - 1)
  have hiff : (EdgeUp (Qof P) li x.edge ↔
      ((Qof P).vtx (x.hgt - 1)).2 < ((Qof P).vtx (y.hgt - 1)).2) ↔
      hltF P (ivB li (Qof P).n x.edge) (ivB li (Qof P).n ((x.edge + 1) % (Qof P).n)) =
        hltF P (x.hgt - 1) (y.hgt - 1) := by
    unfold EdgeUp; rw [← h1, ← h2]; omega
  unfold posLtF PosLt
  rw [hiff]
  split_ifs <;> omega

section pieces

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- `dst := [a = b ∧ c = e]`. -/
theorem eq2S_exec (d : Config) (hw : WordsBounded W d) {a b c e dst : ℕ} (ha : a ≠ dst)
    (hb : b ≠ dst) (hc : c ≠ dst) (he : e ≠ dst) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W (eq2S a b c e dst) d d' k ∧ k ≤ 10 ∧
      NRegs d d' (upd d.nreg dst
        (if d.nreg a = d.nreg b ∧ d.nreg c = d.nreg e then 1 else 0)) := by
  unfold eq2S
  refine x_mono (x_seq (K₂ := 9) (x_const d hw dst 0 (by omega)) (fun d1 hw1 n1 => ?_)) (by omega)
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (r := dst) (d := d1) (K := 7)
    (fun _ => x_mono (x_skipR d1 hw1 dst) (by omega))
    (fun _ => x_ifR (fun _ => x_mono (x_skipR d1 hw1 dst) (by omega))
      (fun _ => x_ifR (fun _ => x_mono (x_skipR d1 hw1 dst) (by omega))
        (fun _ => x_ifR (fun _ => x_skipR d1 hw1 dst)
          (fun _ => x_const d1 hw1 dst 1 (by omega)))))
  refine ⟨d2, k2, e2, by omega, ?_⟩
  refine ⟨?_, n2.2.1.trans n1.2.1, n2.2.2.1.trans n1.2.2.1, n2.2.2.2.1.trans n1.2.2.2.1,
    n2.2.2.2.2.trans n1.2.2.2.2⟩
  rw [n2.1, n1.1, Machine.upd_upd_same]
  simp only [Machine.upd_other _ _ _ ha, Machine.upd_other _ _ _ hb, Machine.upd_other _ _ _ hc,
    Machine.upd_other _ _ _ he, Machine.upd_same]
  congr 1
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- `dst := posLt (a, b) (c, e)`. -/
theorem posLtOn_exec (d : Config) (hw : WordsBounded W d) {a b c e dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg a < n) (hnW : n ≤ W) (hW : 1 ≤ W) (_ha : a < 217150) (hb : b < 217150)
    (hc : c < 217150) (he : e < 217150) :
    ∃ d' k, Exec P W (posLtOn a b c e dst) d d' k ∧ k ≤ 60 ∧
      d'.nreg dst = posLtF P li n (d.nreg a) (d.nreg b) (d.nreg c) (d.nreg e) := by
  unfold posLtOn
  obtain ⟨d1, k1, e1, hk1, a50, a51, a52, a53, g1⟩ : ∃ d1 k1, Exec P W (block [.copyN 217150 a,
      .copyN 217151 b, .copyN 217152 c, .copyN 217153 e]) d d1 k1 ∧ k1 ≤ 4 ∧
      d1.nreg 217150 = d.nreg a ∧ d1.nreg 217151 = d.nreg b ∧ d1.nreg 217152 = d.nreg c ∧
      d1.nreg 217153 = d.nreg e ∧ (∀ r, r < 217150 → d1.nreg r = d.nreg r) := by
    exec_block
    refine ⟨by omega, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> config_simp
    · rw [Machine.upd_other _ _ _ (show b ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show c ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show c ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show e ≠ 217152 by omega),
        Machine.upd_other _ _ _ (show e ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show e ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show r ≠ 217153 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217152 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217150 by omega)]
  obtain ⟨d2, k2, e2, hk2, v2, -⟩ := posLtS_exec (P := P) d1 e1.wb_right
    (by rw [g1 _ (by omega), h20]) (by rw [g1 _ (by omega), h26]) (by rw [g1 _ (by omega), h27])
    (by rw [a50]; exact hae) hnW hW
  obtain ⟨d3, k3, e3, hk3, n3⟩ := x_copy (P := P) d2 e2.wb_right dst 217154
  refine ⟨d3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, ?_⟩
  rw [n3.same, v2, a50, a51, a52, a53]

set_option maxHeartbeats 2000000 in
/-- The arc test `onS` on bits. -/
theorem onS_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) (h27 : d.nreg 217027 = 1) :
    ∃ d' k, Exec P W onS d d' k ∧ k ≤ 16 ∧
      NRegs d d' (upd d.nreg 217127 (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        (if d.nreg 217124 < 1 then (if d.nreg 217125 < 1 then (if d.nreg 217126 < 1 then 0 else 1)
          else 1) else (if d.nreg 217125 < 1 then 0 else (if d.nreg 217126 < 1 then 0 else 1)))
        else 1) else 1)) := by
  unfold onS
  refine x_mono (x_seq (K₂ := 15) (x_const d hw 217127 0 (by omega)) (fun d1 hw1 n1 => ?_))
    (by omega)
  have s0 := fun (K : ℕ) (hK : 1 ≤ K) => x_mono (P := P) (x_skipR d1 hw1 217127) hK
  have s1 := fun (K : ℕ) (hK : 1 ≤ K) => x_mono (P := P) (x_const d1 hw1 217127 1 (by omega)) hK
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (r := 217127) (d := d1) (K := 13)
    (fun _ => x_ifR (fun _ => x_ifR
        (fun _ => x_ifR (fun _ => x_ifR (fun _ => s0 5 (by omega)) (fun _ => s1 5 (by omega)))
          (fun _ => s1 7 (by omega)))
        (fun _ => x_ifR (fun _ => s0 7 (by omega))
          (fun _ => x_ifR (fun _ => s0 5 (by omega)) (fun _ => s1 5 (by omega)))))
      (fun _ => s1 11 (by omega)))
    (fun _ => s1 13 (by omega))
  refine ⟨d2, k2, e2, by omega, ?_⟩
  refine ⟨?_, n2.2.1.trans n1.2.1, n2.2.2.1.trans n1.2.2.1, n2.2.2.2.1.trans n1.2.2.2.1,
    n2.2.2.2.2.trans n1.2.2.2.2⟩
  rw [n2.1, n1.1, Machine.upd_upd_same]
  config_simp
  simp only [h27]

/-- The registers `bktFS` writes. -/
def BbktF (r : ℕ) : Bool := decide (r = 217112 ∨ r = 217128)

theorem wr_bktF : wr BbktF bktFS = true := by decide

set_option maxHeartbeats 2000000 in
/-- **The bucket formula.** -/
theorem bktFS_exec (d : Config) (hw : WordsBounded W d) {A j : ℕ} (hj : j < A)
    (hAW : 2 * A + 2 ≤ W) (h27 : d.nreg 217027 = 1) (h30 : d.nreg 217030 = A)
    (h44 : d.nreg 217044 = 2) (h16 : d.nreg 217116 = j) :
    ∃ d' k, Exec P W bktFS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217112 = (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        (if d.nreg 217125 < 1 then 0 else 2 * j + 2) else 2 * ((j + 1) % A) + 1) else 2 * j + 1) ∧
      FrameB BbktF d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W bktFS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217112 = (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        (if d.nreg 217125 < 1 then 0 else 2 * j + 2) else 2 * ((j + 1) % A) + 1)
          else 2 * j + 1) := by
    unfold bktFS
    by_cases c1 : d.nreg 217122 < 1
    · refine spec_ifLtN_true (by rw [h27]; exact c1) ?_
      by_cases c2 : d.nreg 217123 < 1
      · refine spec_ifLtN_true (by rw [h27]; exact c2) ?_
        by_cases c3 : d.nreg 217125 < 1
        · refine spec_ifLtN_true (by rw [h27]; exact c3) ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_⟩; config_simp; rw [ite_eq_left c1, ite_eq_left c2, ite_eq_left c3]
        · refine spec_ifLtN_false (by rw [h27]; exact c3) ?_
          exec_block
          · omega
          · config_simp; omega
          · refine ⟨by omega, ?_⟩; config_simp; rw [ite_eq_left c1, ite_eq_left c2, ite_eq_right c3]; omega
      · refine spec_ifLtN_false (by rw [h27]; exact c2) ?_
        refine spec_seq ?_
        exec_block
        · omega
        by_cases c4 : j + 1 < A
        · refine spec_ifLtN_true (by config_simp; omega) ?_
          exec_block
          · config_simp; omega
          · config_simp; omega
          · refine ⟨by omega, ?_⟩; config_simp
            rw [ite_eq_left c1, ite_eq_right c2, Nat.mod_eq_of_lt c4]; omega
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_⟩; config_simp
            have h0 : (j + 1) % A = 0 := by rw [show j + 1 = A by omega, Nat.mod_self]
            rw [ite_eq_left c1, ite_eq_right c2, h0]
    · refine spec_ifLtN_false (by rw [h27]; exact c1) ?_
      exec_block
      · omega
      · config_simp; omega
      · refine ⟨by omega, ?_⟩; config_simp; rw [ite_eq_right c1]; omega
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_bktF⟩

/-- The registers `arcRdS` writes. -/
def Brd (r : ℕ) : Bool := decide ((217116 ≤ r ∧ r ≤ 217121) ∨ r = 217128)

theorem wr_arcRd : wr Brd arcRdS = true := by decide

set_option maxHeartbeats 2000000 in
/-- **Read arc `j`** (the region list entry at `217114`). -/
theorem arcRd_exec (d : Config) (hw : WordsBounded W d) {AB j se sh ee eh : ℕ}
    (h14 : d.nmem (d.nreg 217114) = j) (h27 : d.nreg 217027 = 1) (h31 : d.nreg 217031 = AB)
    (hAW : AB + 5 * j + 4 ≤ W) (m1 : d.nmem (AB + 5 * j + 1) = se)
    (m2 : d.nmem (AB + 5 * j + 2) = sh) (m3 : d.nmem (AB + 5 * j + 3) = ee)
    (m4 : d.nmem (AB + 5 * j + 4) = eh) :
    ∃ d' k, Exec P W arcRdS d d' k ∧ k ≤ 13 ∧ d'.nreg 217116 = j ∧ d'.nreg 217118 = se ∧
      d'.nreg 217119 = sh ∧ d'.nreg 217120 = ee ∧ d'.nreg 217121 = eh ∧ FrameB Brd d d' := by
  have k1 : ∀ a, a = AB + 5 * j + 1 → d.nmem a = se := fun a ha => ha ▸ m1
  have k2 : ∀ a, a = AB + 5 * j + 2 → d.nmem a = sh := fun a ha => ha ▸ m2
  have k3 : ∀ a, a = AB + 5 * j + 3 → d.nmem a = ee := fun a ha => ha ▸ m3
  have k4 : ∀ a, a = AB + 5 * j + 4 → d.nmem a = eh := fun a ha => ha ▸ m4
  obtain ⟨d', k, ex, hk, v16, v18, v19, v20, v21⟩ : ∃ d' k, Exec P W arcRdS d d' k ∧ k ≤ 13 ∧
      d'.nreg 217116 = j ∧ d'.nreg 217118 = se ∧ d'.nreg 217119 = sh ∧ d'.nreg 217120 = ee ∧
      d'.nreg 217121 = eh := by
    unfold arcRdS
    exec_block
    all_goals (try (config_simp; simp only [h14, h27, h31]; omega))
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h14, h27, h31]
    · exact k1 _ (by omega)
    · exact k2 _ (by omega)
    · exact k3 _ (by omega)
    · exact k4 _ (by omega)
  exact ⟨d', k, ex, hk, v16, v18, v19, v20, v21, exec_frameB ex wr_arcRd⟩

end pieces

end

end DrvX

end Chazelle.Core
