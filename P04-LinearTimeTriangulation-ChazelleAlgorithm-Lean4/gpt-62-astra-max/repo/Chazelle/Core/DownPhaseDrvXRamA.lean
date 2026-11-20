module
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address
public import Chazelle.Programs.Verification

public import Chazelle.Core.DownPhaseDrvXRamDef

/-!
# Down phase, extraction (D6), RAM part 1: height order, walk indices, key order

Executions of `hltS`, `ivBS`, `succS`, `qES`, `posLtS` (their outputs as functions of their
inputs, write sets, cost bounds).
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK

@[expose] public section

open Classical in
/-- The value computed by `hltS`. -/
noncomputable def hltF (P : Polygon) (u v : ℕ) : ℕ :=
  if Mountain.ylexLT (P.vtx u) (P.vtx v) then 1 else 0

/-- The registers `hltS` writes. -/
def Bhlt (r : ℕ) : Bool := decide (r = 217160 ∨ r = 217161 ∨ r = 217162)

theorem wr_hlt : wr Bhlt hltS = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`hltS`**: the height order of the input vertices. -/
theorem hltS_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W hltS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217162 = hltF P (d.nreg 217160) (d.nreg 217161) ∧ FrameB Bhlt d d' := by
  obtain ⟨d', k, ex, hk, h1⟩ : ∃ d' k, Exec P W hltS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217162 = hltF P (d.nreg 217160) (d.nreg 217161) := by
    unfold hltS hltF
    refine spec_seq ?_
    exec_block
    by_cases hy : (P.vtx (d.nreg 217160)).2 < (P.vtx (d.nreg 217161)).2
    · refine spec_ifLtR_true (hy) ?_
      exec_block
      · omega
      · refine ⟨by omega, ?_⟩
        config_simp
        rw [ite_eq_left (show Mountain.ylexLT _ _ from Or.inl hy)]
    · refine spec_ifLtR_false (hy) ?_
      by_cases hy' : (P.vtx (d.nreg 217161)).2 < (P.vtx (d.nreg 217160)).2
      · refine spec_ifLtR_true (hy') ?_
        exec_block
        · omega
        · refine ⟨by omega, ?_⟩
          config_simp
          rw [ite_eq_right (show ¬ Mountain.ylexLT _ _ from ?_)]
          rintro (h | ⟨h, -⟩)
          · exact hy h
          · simp_all
      · refine spec_ifLtR_false (hy') ?_
        refine spec_seq ?_
        exec_block
        by_cases hx : (P.vtx (d.nreg 217160)).1 < (P.vtx (d.nreg 217161)).1
        · refine spec_ifLtR_true (hx) ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_⟩
            config_simp
            rw [ite_eq_left (show Mountain.ylexLT _ _ from Or.inr ⟨(le_antisymm (not_lt.1 hy') (not_lt.1 hy)), hx⟩)]
        · refine spec_ifLtR_false (hx) ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_⟩
            config_simp
            rw [ite_eq_right (show ¬ Mountain.ylexLT _ _ from ?_)]
            rintro (h | ⟨-, h⟩)
            · exact hy h
            · exact hx h
  exact ⟨d', k, ex, hk, h1, exec_frameB ex wr_hlt⟩

/-- The register value of the `li` bit. -/
def liV (li : Bool) : ℕ := if li then 1 else 0

theorem liV_le (li : Bool) : liV li ≤ 1 := by unfold liV; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- **`ivBS`**: `dst := ivB li n src`. -/
theorem ivBS_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hsd : src ≠ dst) (_hd20 : dst ≠ 217020) (_hd27 : dst ≠ 217027) :
    ∃ d' k, Exec P W (ivBS src dst) d d' k ∧ k ≤ 4 ∧
      d'.nreg = upd d.nreg dst (DrvR.ivB li n (d.nreg src)) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold ivBS
  cases li
  · refine spec_ifLtN_true (by grind [liV]) ?_
    refine spec_step (Machine.Exec.subN hw _ _ _) (fun hw₁ => ?_)
    refine spec_step (Machine.Exec.subN hw₁ _ _ _) (fun hw₂ => ?_)
    refine spec_nil hw₂ ⟨by omega, ?_, rfl, rfl, rfl, rfl⟩ <;> grind [Machine.upd_same, Machine.upd_other, Machine.upd_upd_same, DrvR.ivB]
  · refine spec_ifLtN_false (by grind [liV]) ?_
    refine spec_step (Machine.Exec.copyN hw _ _) (fun hw₁ => ?_)
    refine spec_nil hw₁ ⟨by omega, ?_, rfl, rfl, rfl, rfl⟩
    rfl

set_option maxHeartbeats 1000000 in
/-- **`succS`**: `dst := (src + 1) mod n` for `src < n`. -/
theorem succS_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (hs : d.nreg src < n) (hnW : n ≤ W)
    (hd20 : dst ≠ 217020) :
    ∃ d' k, Exec P W (succS src dst) d d' k ∧ k ≤ 4 ∧
      d'.nreg = upd d.nreg dst ((d.nreg src + 1) % n) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold succS
  refine spec_seq ?_
  refine spec_step (guarded (Machine.Exec.addN hw _ _ _)) (fun hw₁ => ?_)
  refine spec_nil hw₁ ?_
  by_cases h : d.nreg src + 1 < n
  · refine spec_ifLtN_true (by block_post) ?_
    refine spec_skip hw₁ ⟨by omega, ?_, rfl, rfl, rfl, rfl⟩
    grind [Nat.mod_eq_of_lt]
  · refine spec_ifLtN_false (by grind [Machine.upd_same, Machine.upd_other]) ?_
    refine spec_step (guarded (Machine.Exec.constN hw₁ _ _)) (fun hw₂ => ?_)
    refine spec_nil hw₂ ⟨by omega, ?_, rfl, rfl, rfl, rfl⟩ <;> grind [Machine.upd_upd_same, Nat.mod_self]

set_option maxHeartbeats 1000000 in
/-- **`qES`**: `dst := qE li n src` (scratch `217104`). -/
theorem qES_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hs : d.nreg src < n) (hnW : n ≤ W) (hsd : src ≠ dst) (_hd20 : dst ≠ 217020)
    (hd27 : dst ≠ 217027) (_hd04 : dst ≠ 217104) (hs04 : src ≠ 217104) :
    ∃ d' k, Exec P W (qES src dst) d d' k ∧ k ≤ 8 ∧
      d'.nreg dst = DrvR.qE li n (d.nreg src) ∧
      (∀ r, r ≠ dst → r ≠ 217104 → d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold qES
  cases li
  · refine spec_ifLtN_true (by rw [h26, h27]; simp [liV]) ?_
    refine spec_seq ?_
    refine spec_step (Machine.Exec.addN hw _ _ _ (by rw [h27]; omega)) (fun hw₁ => ?_)
    refine spec_nil hw₁ ?_
    set f := upd d.nreg 217104 (d.nreg src + d.nreg 217027) with hf
    have g : ∀ r, r ≠ 217104 → f r = d.nreg r := fun r hr => Machine.upd_other _ _ _ hr
    have g04 : f 217104 = d.nreg src + 1 := by simp_all
    have g20 : f 217020 = n := by simp_all
    have g27 : f 217027 = 1 := by simp_all
    by_cases h : d.nreg src + 1 < n
    · refine spec_ifLtN_true (by simp_all) ?_
      refine spec_step (Machine.Exec.subN hw₁ _ _ _) (fun hw₂ => ?_)
      refine spec_step (Machine.Exec.subN hw₂ _ _ _) (fun hw₃ => ?_)
      refine spec_step (Machine.Exec.subN hw₃ _ _ _) (fun hw₄ => ?_)
      refine spec_nil hw₄ ⟨by omega, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · simp only [Machine.upd_same, Machine.upd_upd_same,
          Machine.upd_other _ _ _ hsd, Machine.upd_other _ _ _ hd27.symm, g20, g27, (g src hs04), DrvR.qE, Bool.false_eq_true, ite_false,
          ite_eq_left h]
        omega
      · simp only [Machine.upd_other _ _ _ h1, g _ h2]
    · refine spec_ifLtN_false (by simp_all) ?_
      refine spec_step (Machine.Exec.subN hw₁ _ _ _) (fun hw₂ => ?_)
      refine spec_nil hw₂ ⟨by omega, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · simp only [Machine.upd_same, g20, g27, DrvR.qE, Bool.false_eq_true,
          ite_false, ite_eq_right h]
      · simp_all
  · refine spec_ifLtN_false (by rw [h26, h27]; simp [liV]) ?_
    refine spec_step (Machine.Exec.copyN hw _ _) (fun hw₁ => ?_)
    refine spec_nil hw₁ ⟨by omega, ?_, fun r h1 _ => ?_, rfl, rfl, rfl, rfl⟩
    · simp [DrvR.qE]
    · simp_all

open Classical in
/-- The value computed by `posLtS`. -/
noncomputable def posLtF (P : Polygon) (li : Bool) (n ae ah be bh : ℕ) : ℕ :=
  if ae < be then 1 else if be < ae then 0 else if ah = bh then 0 else
    if hltF P (DrvR.ivB li n ae) (DrvR.ivB li n ((ae + 1) % n)) = hltF P (ah - 1) (bh - 1) then 1
    else 0

/-- The registers `posLtS` writes. -/
def BposLt (r : ℕ) : Bool :=
  decide (r = 217154 ∨ r = 217155 ∨ r = 217156 ∨ r = 217160 ∨ r = 217161 ∨ r = 217162)

theorem wr_posLt : wr BposLt posLtS = true := by decide

set_option maxHeartbeats 2000000 in
/-- The core of `posLtS`. -/
theorem posLtCore_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg 217150 < n) (hnW : n ≤ W) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W posLtCore d d' k ∧ k ≤ 45 ∧
      d'.nreg 217154 = (if hltF P (DrvR.ivB li n (d.nreg 217150))
        (DrvR.ivB li n ((d.nreg 217150 + 1) % n)) = hltF P (d.nreg 217151 - 1) (d.nreg 217153 - 1)
        then 1 else 0) := by
  -- `u1 := ivB ae`
  obtain ⟨d1, k1, e1, hk1, n1, r1, m1, -, -⟩ := guarded (ivBS_exec (P := P) d hw (src := 217150)
    (dst := 217160) h20 h26 h27)
  have v1 : AgreeExcept [217160] d1.nreg d.nreg := fun r hr => by simp_all
  -- `q1 := (ae + 1) mod n`
  obtain ⟨d2, k2, e2, hk2, n2, -, -, -, -⟩ := succS_exec (P := P) d1 e1.wb_right (src := 217150)
    (dst := 217155) (by simp_all) (by simp_all)
    (by simp_all) hnW (by decide)
  have v2 : AgreeExcept [217155] d2.nreg d1.nreg := fun r hr => by simp_all
  -- `u2 := ivB q1`
  obtain ⟨d3, k3, e3, hk3, n3, -, -, -, -⟩ := ivBS_exec (P := P) d2 e2.wb_right (src := 217155)
    (dst := 217161) (rfl)
    (by rw [v2 _ (by decide), v1 _ (by decide), h26]) (by simp_all)
    (by decide) (by decide) (by decide)
  have v3 : ∀ r, r ≠ 217161 → d3.nreg r = d2.nreg r := fun r hr => by simp_all
  have a160 : d3.nreg 217160 = DrvR.ivB li n (d.nreg 217150) := by
    simp_all
  have a161 : d3.nreg 217161 = DrvR.ivB li n ((d.nreg 217150 + 1) % n) := by
    simp_all
  -- `up`
  obtain ⟨d4, k4, e4, hk4, up4, f4⟩ := hltS_exec (P := P) d3 e3.wb_right hW
  have g4 : ∀ r, Bhlt r = false → r ≠ 217155 → d4.nreg r = d.nreg r := fun r hr h55 => by
    rw [f4.1 r hr, at_index v3 r,
      v2 r h55, at_index v1 r]
  -- heights
  obtain ⟨d5, k5, e5, hk5, a56, a60, a61, g5⟩ : ∃ d5 k5, Exec P W (block [.copyN 217156 217162,
      .subN 217160 217151 217027, .subN 217161 217153 217027]) d4 d5 k5 ∧ k5 = 3 ∧
      d5.nreg 217156 = d4.nreg 217162 ∧ d5.nreg 217160 = d.nreg 217151 - 1 ∧
      d5.nreg 217161 = d.nreg 217153 - 1 ∧
      (∀ r, r ≠ 217156 → r ≠ 217160 → r ≠ 217161 → d5.nreg r = d4.nreg r) := by
    have hw4 := e4.wb_right
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩ <;> config_simp
    · rw [g4 _ (by decide) (by decide), g4 _ (by decide) (by decide), h27]
    · rw [g4 _ (by decide) (by decide), g4 _ (by decide) (by decide), h27]
    · simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h3]
  -- `hc`
  obtain ⟨d6, k6, e6, hk6, hc6, f6⟩ := hltS_exec (P := P) d5 e5.wb_right hW
  have b56 : d6.nreg 217156 = hltF P (DrvR.ivB li n (d.nreg 217150))
      (DrvR.ivB li n ((d.nreg 217150 + 1) % n)) := by
    rw [f6.1 _ (by decide), a56, up4, a160, a161]
  rw [a60, a61] at hc6
  -- the comparison
  obtain ⟨d7, k7, e7, hk7, h7⟩ : ∃ d7 k7, Exec P W (.ifLtN 217156 217162 (block [.constN 217154 0])
      (.ifLtN 217162 217156 (block [.constN 217154 0]) (block [.constN 217154 1]))) d6 d7 k7 ∧
      k7 ≤ 5 ∧ d7.nreg 217154 = (if d6.nreg 217156 = d6.nreg 217162 then 1 else 0) := by
    have hw6 := e6.wb_right
    by_cases c1 : d6.nreg 217156 < d6.nreg 217162
    · refine spec_ifLtN_true c1 ?_
      exec_block
      · omega
      · refine ⟨by omega, ?_⟩; config_simp; rw [guarded ite_eq_right]
    · refine spec_ifLtN_false c1 ?_
      by_cases c2 : d6.nreg 217162 < d6.nreg 217156
      · refine spec_ifLtN_true c2 ?_
        exec_block
        · omega
        · refine ⟨by omega, ?_⟩; config_simp; rw [guarded ite_eq_right]
      · refine spec_ifLtN_false c2 ?_
        exec_block
        · omega
        · refine ⟨by omega, ?_⟩; config_simp; grind
  refine ⟨d7, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + k7))))),
    e1 ;; e2 ;; e3 ;; e4 ;; e5 ;; e6 ;; e7, by omega, ?_⟩
  rw [h7, b56, hc6]

set_option maxHeartbeats 2000000 in
/-- **`posLtS`**: the key order of two interior positions. -/
theorem posLtS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg 217150 < n) (hnW : n ≤ W) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W posLtS d d' k ∧ k ≤ 52 ∧
      d'.nreg 217154 = posLtF P li n (d.nreg 217150) (d.nreg 217151) (d.nreg 217152)
        (d.nreg 217153) ∧ FrameB BposLt d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W posLtS d d' k ∧ k ≤ 52 ∧
      d'.nreg 217154 = posLtF P li n (d.nreg 217150) (d.nreg 217151) (d.nreg 217152)
        (d.nreg 217153) := by
    unfold posLtS posLtF
    by_cases c1 : d.nreg 217150 < d.nreg 217152
    · refine spec_ifLtN_true c1 ?_
      exec_block
      · omega
      · simp_all
    · refine spec_ifLtN_false c1 ?_
      by_cases c2 : d.nreg 217152 < d.nreg 217150
      · refine spec_ifLtN_true c2 ?_
        exec_block
        · omega
        · simp_all
      · refine spec_ifLtN_false c2 ?_
        by_cases c3 : d.nreg 217151 < d.nreg 217153
        · refine spec_ifLtN_true c3 ?_
          refine spec_use (posLtCore_exec d hw h20 h26 h27 hae hnW hW) ?_ <;> grind
        · refine spec_ifLtN_false c3 ?_
          by_cases c4 : d.nreg 217153 < d.nreg 217151
          · refine spec_ifLtN_true c4 ?_
            refine spec_use (posLtCore_exec d hw h20 h26 h27 hae hnW hW) ?_ <;> grind
          · refine spec_ifLtN_false c4 ?_
            exec_block
            · omega
            · refine ⟨by omega, ?_⟩; config_simp; grind
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_posLt⟩

end exec

end

end DrvX

end Chazelle.Core
