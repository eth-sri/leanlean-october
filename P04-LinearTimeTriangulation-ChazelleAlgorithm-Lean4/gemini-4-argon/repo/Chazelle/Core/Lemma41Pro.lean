module

public import Chazelle.Core.Lemma41Tab

/-!
# WP-J, part 23: the prologue of Lemma 4.1

* `proC`: the constants;
* `proL`: the registers of the cover loop (from the grade record: halving table, powers, row
  table), the bound `G₀ = γ'_{λ-1}` of the leaves (from the oracle record of chain `(λ-1, 0)`) and
  `2^⌈βλ⌉` (from the setup tables);
* `clogS`: `⌈log₂ λ⌉` by scanning the powers; `mulS`: `Gλ = γ'_λ = 2^⌈βλ⌉ + λ (⌈log₂ λ⌉ + 2)`;
* `proH`: the whole host `[run 0 (n-1)]` at the allocator (seven words reserved), the record
  pointer `R₀` just above it.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle

@[expose] public section

/-- The constants. -/
def proC : Stmt := block [.constN 160024 1, .constN 160080 2, .constN 160081 5, .constN 160082 6,
  .constN 160083 3, .constN 160084 4, .constN 160086 7, .constN 160087 8, .constN 160029 0]

/-- The registers of the cover and the table reads. -/
def proL : Stmt := block [.copyN 160010 160001, .addN 160011 160001 160002,
  .copyN 160026 160003,
  .addN 160031 160000 160083, .loadN 160020 160031,
  .addN 160031 160000 160024, .loadN 160101 160031,
  .addN 160021 160101 160080,
  .addN 160031 160000 160080, .loadN 160022 160031,
  .addN 160031 160022 160003, .subN 160031 160031 160024, .loadN 160031 160031,
  .addN 160031 160031 160080, .loadN 160031 160031, .addN 160031 160031 160080,
  .loadN 160033 160031,
  .addN 160031 160101 160024, .loadN 160102 160031, .addN 160031 160101 160102,
  .addN 160031 160031 160084, .addN 160031 160031 160003, .loadN 160103 160031,
  .addN 160031 160021 160103, .loadN 160032 160031, .constN 160014 0]

/-- `⌈log₂ λ⌉` in `160104`, by scanning the powers of two. -/
def clogS : Stmt := .seq (block [.constN 160104 0, .loadN 160105 160021])
  (.whileLtN 160105 160003 (block [.addN 160104 160104 160024, .addN 160031 160021 160104,
    .loadN 160105 160031]))

/-- `Gλ = 2^⌈βλ⌉ + λ (⌈log₂ λ⌉ + 2)` in `160032`. -/
def mulS : Stmt := .seq (block [.addN 160106 160104 160080, .constN 160107 0, .constN 160108 0])
  (.seq (.whileLtN 160108 160003 (block [.addN 160107 160107 160106, .addN 160108 160108 160024]))
    (block [.addN 160032 160032 160107]))

/-- The whole host at the allocator; the record pointer above it. -/
def proH : Stmt := block [.copyN 160027 9999, .inputSize 160028, .subN 160028 160028 160024,
  .storeN 160027 160024, .addN 160030 160027 160024, .storeN 160030 160029,
  .addN 160030 160030 160024, .storeN 160030 160029, .addN 160030 160030 160024,
  .storeN 160030 160028, .addN 9999 9999 160086, .copyN 160015 9999]

/-- The registers written by `proL`. -/
def ProRG (r : ℕ) : Prop :=
  r = 160010 ∨ r = 160011 ∨ r = 160014 ∨ r = 160020 ∨ r = 160021 ∨ r = 160022 ∨
    r = 160026 ∨ (160031 ≤ r ∧ r ≤ 160033) ∨ (160101 ≤ r ∧ r ≤ 160103)

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem proC_exec {c : Config} (hw : WordsBounded W c) (hW : 8 ≤ W) :
    ∃ c' k, Exec P W proC c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160024 = 1 ∧ c'.nreg 160080 = 2 ∧ c'.nreg 160081 = 5 ∧ c'.nreg 160082 = 6 ∧
      c'.nreg 160083 = 3 ∧ c'.nreg 160084 = 4 ∧ c'.nreg 160086 = 7 ∧ c'.nreg 160087 = 8 ∧
      c'.nreg 160029 = 0 ∧
      (∀ r, (r < 160024 ∨ (160029 < r ∧ r < 160080) ∨ 160087 < r ∨
        (160024 < r ∧ r < 160029) ∨ r = 160085) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold proC
  exec_block
  all_goals try omega
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 16000000 in
theorem proL_exec {c : Config} (hw : WordsBounded W c) {h a L lam : ℕ}
    (h00 : c.nreg 160000 = h) (h01 : c.nreg 160001 = a) (h02 : c.nreg 160002 = L)
    (h03 : c.nreg 160003 = lam) (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4) (hl : 1 ≤ lam)
    (hW1 : h + 3 ≤ W) (hW2 : a + L ≤ W) (hW3 : c.nmem (h + 1) + 2 ≤ W)
    (hW4 : c.nmem (h + 2) + lam ≤ W)
    (hW5 : c.nmem (c.nmem (h + 2) + lam - 1) + 2 ≤ W)
    (hW6 : c.nmem (c.nmem (c.nmem (h + 2) + lam - 1) + 2) + 2 ≤ W)
    (hW7 : c.nmem (h + 1) + c.nmem (c.nmem (h + 1) + 1) + 4 + lam ≤ W)
    (hW8 : c.nmem (h + 1) + 2 + c.nmem (c.nmem (h + 1) + c.nmem (c.nmem (h + 1) + 1) + 4 + lam)
      ≤ W) :
    ∃ c' k, Exec P W proL c c' k ∧ k = 26 ∧ WordsBounded W c' ∧
      c'.nreg 160010 = a ∧ c'.nreg 160011 = a + L ∧ c'.nreg 160026 = lam ∧
      c'.nreg 160020 = c.nmem (h + 3) ∧ c'.nreg 160101 = c.nmem (h + 1) ∧
      c'.nreg 160021 = c.nmem (h + 1) + 2 ∧ c'.nreg 160022 = c.nmem (h + 2) ∧
      c'.nreg 160033 = c.nmem (c.nmem (c.nmem (c.nmem (h + 2) + lam - 1) + 2) + 2) ∧
      c'.nreg 160102 = c.nmem (c.nmem (h + 1) + 1) ∧
      c'.nreg 160103 = c.nmem (c.nmem (h + 1) + c.nmem (c.nmem (h + 1) + 1) + 4 + lam) ∧
      c'.nreg 160032 = c.nmem (c.nmem (h + 1) + 2 +
        c.nmem (c.nmem (h + 1) + c.nmem (c.nmem (h + 1) + 1) + 4 + lam)) ∧
      c'.nreg 160014 = 0 ∧
      (∀ r, ¬ ProRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold proL
  exec_block
  all_goals try (config_simp; (try simp only [h00, h01, h02, h03, h24, h80, h83, h84]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  · config_simp; simp only [h01]
  · config_simp; simp only [h01, h02]
  · config_simp; simp only [h03]
  · config_simp; simp only [h00, h83]
  · config_simp; simp only [h00, h24]
  · config_simp; simp only [h00, h24, h80]
  · config_simp; simp only [h00, h80]
  · config_simp; simp only [h00, h03, h24, h80]
  · config_simp; simp only [h00, h24]
  · config_simp; simp only [h00, h03, h24, h84]
  · config_simp; simp only [h00, h03, h24, h80, h84]
  · config_simp
  · unfold ProRG at hr
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

/-- `⌈log₂ λ⌉` is the first `c` with `λ ≤ 2^c`. -/
theorem clog_eq_of {lam c : ℕ} (h1 : lam ≤ 2 ^ c) (h2 : c ≤ Nat.clog 2 lam) :
    c = Nat.clog 2 lam := le_antisymm h2 (Nat.clog_le_of_le_pow h1)

set_option maxHeartbeats 8000000 in
theorem clogS_exec {c : Config} (hw : WordsBounded W c) {PW lam : ℕ}
    (h21 : c.nreg 160021 = PW) (h03 : c.nreg 160003 = lam) (h24 : c.nreg 160024 = 1)
    (hpow : ∀ i, i ≤ lam → c.nmem (PW + i) = 2 ^ i) (hl : 1 ≤ lam) (hW : PW + lam ≤ W) :
    ∃ c' k, Exec P W clogS c c' k ∧ k ≤ 5 * lam + 4 ∧ WordsBounded W c' ∧
      c'.nreg 160104 = Nat.clog 2 lam ∧
      (∀ r, r ≠ 160104 → r ≠ 160105 → r ≠ 160031 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcl : Nat.clog 2 lam ≤ lam := by
    exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  obtain ⟨c1, k1, e1, hk1, hw1, i04, i05, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 160104 0, .loadN 160105 160021]) c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 160104 = 0 ∧ c1.nreg 160105 = 2 ^ 0 ∧
      (∀ r, r ≠ 160104 → r ≠ 160105 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ‹_›, by config_simp, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [h21]; have := hpow 0 (by omega); simpa using this
    · simp only
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ ∃ i, i ≤ Nat.clog 2 lam ∧
    c'.nreg 160104 = i ∧ c'.nreg 160105 = 2 ^ i ∧
    (∀ r, r ≠ 160104 → r ≠ 160105 → r ≠ 160031 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨hw', i, hi, h04, h05, fr', hm', hrr', hrm', ho'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 160105) (b := 160003)
      (body := block [.addN 160104 160104 160024, .addN 160031 160021 160104,
        .loadN 160105 160031]) I (fun c' => 5 * (Nat.clog 2 lam - c'.nreg 160104))
      (fun c' h => h.1)
      (fun c2 ⟨hw2, i, hi, h04, h05, fr2, hm2, hrr2, hrm2, ho2⟩ htest => by
        have c03 : c2.nreg 160003 = lam := by rw [fr2 _ (by omega) (by omega) (by omega)]; exact h03
        have c21 : c2.nreg 160021 = PW := by rw [fr2 _ (by omega) (by omega) (by omega)]; exact h21
        have c24 : c2.nreg 160024 = 1 := by rw [fr2 _ (by omega) (by omega) (by omega)]; exact h24
        rw [h05, c03] at htest
        have hil : i < Nat.clog 2 lam := by
          by_contra hc
          have := Nat.le_pow_clog (b := 2) (by norm_num) lam
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
          omega
        obtain ⟨c3, k3, e3, hk3, hw3, q04, q05, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
            (block [.addN 160104 160104 160024, .addN 160031 160021 160104, .loadN 160105 160031])
            c2 c3 k3 ∧ k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 160104 = i + 1 ∧
            c3.nreg 160105 = 2 ^ (i + 1) ∧
            (∀ r, r ≠ 160104 → r ≠ 160105 → r ≠ 160031 → c3.nreg r = c2.nreg r) ∧
            c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧
            c3.output = c2.output := by
          exec_block
          all_goals try (config_simp; (try simp only [h04, c21, c24]); omega)
          refine ⟨rfl, ‹_›, by config_simp; simp only [h04, c24], ?_, fun r a1 a2 a3 => ?_, rfl,
            rfl, rfl, rfl⟩
          · config_simp; simp only [h04, c21, c24, hm2]; exact hpow (i + 1) (by omega)
          · simp only
            repeat (rw [Machine.upd_other _ _ _ (by omega)])
        refine ⟨c3, k3, e3, ⟨hw3, i + 1, by omega, q04, q05,
          fun r a1 a2 a3 => by rw [fr3 r a1 a2 a3]; exact fr2 r a1 a2 a3, by rw [hm3, hm2],
          by rw [hrr3, hrr2], by rw [hrm3, hrm2], by rw [ho3, ho2]⟩, ?_⟩
        show 5 * (Nat.clog 2 lam - c3.nreg 160104) + k3 + 2 ≤ 5 * (Nat.clog 2 lam - c2.nreg 160104)
        rw [q04, h04]; omega)
      ⟨hw1, 0, Nat.zero_le _, i04, i05, fun r a1 a2 _ => fr1 r a1 a2, hm1, hrr1, hrm1, ho1⟩
  have c03 : c'.nreg 160003 = lam := by rw [fr' _ (by omega) (by omega) (by omega)]; exact h03
  rw [h05, c03] at htest
  have hk' : k ≤ 5 * Nat.clog 2 lam + 2 := by
    have := hk; simp only [i04, Nat.sub_zero] at this; exact this
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', ?_, fr', hm', hrr', hrm', ho'⟩
  rw [h04]; exact clog_eq_of (by omega) hi

set_option maxHeartbeats 8000000 in
theorem mulS_exec {c : Config} (hw : WordsBounded W c) {lam cl G2 : ℕ}
    (h04 : c.nreg 160104 = cl) (h03 : c.nreg 160003 = lam) (h32 : c.nreg 160032 = G2)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (hW : G2 + lam * (cl + 2) + cl + 2 ≤ W) :
    ∃ c' k, Exec P W mulS c c' k ∧ k ≤ 4 * lam + 6 ∧ WordsBounded W c' ∧
      c'.nreg 160032 = G2 + lam * (cl + 2) ∧
      (∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, i06, i07, i08, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 160106 160104 160080, .constN 160107 0, .constN 160108 0]) c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160106 = cl + 2 ∧ c1.nreg 160107 = 0 ∧ c1.nreg 160108 = 0 ∧
      (∀ r, r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h04, h80]); omega)
    refine ⟨rfl, ‹_›, by config_simp; simp only [h04, h80], by config_simp, by config_simp,
      fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  obtain ⟨c2, k2, e2, hk2, hw2, -, -, h07, fr2, hm2, hrr2, hrm2, ho2⟩ :=
    forN (P := P) (W := W) (ri := 160108) (rn := 160003)
      (body := block [.addN 160107 160107 160106, .addN 160108 160108 160024])
      (fun i c' => WordsBounded W c' ∧ c'.nreg 160108 = i ∧ c'.nreg 160003 = lam ∧
        c'.nreg 160107 = i * (cl + 2) ∧
        (∀ r, r ≠ 160107 → r ≠ 160108 → c'.nreg r = c1.nreg r) ∧ c'.nmem = c1.nmem ∧
        c'.rreg = c1.rreg ∧ c'.rmem = c1.rmem ∧ c'.output = c1.output)
      lam 2 (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun i c2 hi ⟨hw2, h08, c03, h07, fr2, hm2, hrr2, hrm2, ho2⟩ => by
        have c06 : c2.nreg 160106 = cl + 2 := by rw [fr2 _ (by omega) (by omega)]; exact i06
        have c24 : c2.nreg 160024 = 1 := by
          rw [fr2 _ (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega)]; exact h24
        have hbound : (i + 1) * (cl + 2) ≤ lam * (cl + 2) := Nat.mul_le_mul_right _ (by omega)
        exec_block
        all_goals try (config_simp; (try simp only [h08, h07, c06, c24]); nlinarith)
        refine ⟨by omega, ‹_›, by config_simp; simp only [h08, c24], c03 ▸ by config_simp, ?_,
          fun r a1 a2 => ?_, hm2, hrr2, hrm2, ho2⟩
        · config_simp; simp only [h07, c06]; ring
        · simp only
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
          exact fr2 r a1 a2)
      (j₀ := 0) ⟨hw1, i08, by rw [fr1 _ (by omega) (by omega) (by omega)]; exact h03,
        by rw [i07]; ring, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Nat.zero_le _)
  obtain ⟨c3, k3, e3, hk3, hw3, q32, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.addN 160032 160032 160107]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 160032 = G2 + lam * (cl + 2) ∧ (∀ r, r ≠ 160032 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    have c32 : c2.nreg 160032 = G2 := by
      rw [fr2 _ (by omega) (by omega), fr1 _ (by omega) (by omega) (by omega)]; exact h32
    exec_block
    all_goals try (config_simp; (try simp only [c32, h07]); nlinarith)
    refine ⟨rfl, ‹_›, by config_simp; simp only [c32, h07], fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  refine ⟨c3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, hw3, q32,
    fun r a1 a2 a3 a4 => ?_, by rw [hm3, hm2, hm1], by rw [hrr3, hrr2, hrr1],
    by rw [hrm3, hrm2, hrm1], by rw [ho3, ho2, ho1]⟩
  rw [fr3 r a1, fr2 r a3 a4, fr1 r a2 a3 a4]

set_option maxHeartbeats 16000000 in
theorem proH_exec {c : Config} (hw : WordsBounded W c) {A : ℕ}
    (hA : c.nreg ALLOC = A) (h24 : c.nreg 160024 = 1) (h29 : c.nreg 160029 = 0)
    (h86 : c.nreg 160086 = 7) (hn : 1 ≤ P.n) (hW : A + 7 ≤ W) (hWn : P.n ≤ W) :
    ∃ c' k, Exec P W proH c c' k ∧ k = 12 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 7 ∧ c'.nreg 160027 = A ∧ c'.nreg 160015 = A + 7 ∧
      HostAt c'.nmem A (Host.whole P.n) ∧
      (∀ a, (a < A ∨ A + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 160027 → r ≠ 160028 → r ≠ 160030 → r ≠ 160015 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold proH
  exec_block
  all_goals try (config_simp; (try simp only [hA, h24, h29, h86]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ⟨?_, fun i hi => ?_⟩, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h86]
  · config_simp; simp only [hA]
  · config_simp; simp only [hA, h86]
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega | simp [Host.whole]
  · have hi0 : i = 0 := by simp [Host.whole] at hi; omega
    subst hi0
    simp only [Host.whole, List.getD_cons_zero]
    simp only [hA, h24, h29, Machine.upd_apply]
    refine ⟨?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega)
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

end proofs

end

end Chazelle.Core.L41
