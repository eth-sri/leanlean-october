module

public import Chazelle.Core.UpPhase20
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 16000000

/-!
# WP-J up phase, part 21: the initialisation

* `initA`: the constants, the setup handle `S = coreReg 0`, `n`, `p = m (S + 1)`, `p + 1`,
  `n - 1`;
* `initH`: the whole host (`proH` of Lemma 4.1) in `170004`;
* `initR`: the record `[0, S, h + 4, D]` of grade `0` and the registers of grade `0`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The constants and the setup data. -/
def initA : Stmt := block [.constN 170020 1, .constN 170021 2, .constN 170022 3,
  .constN 170023 5, .constN 170025 4, .constN 170026 6, .constN 170029 0, .constN 170037 7,
  .copyN 170000 230000, .inputSize 170001, .addN 170053 170000 170020, .loadN 170002 170053,
  .addN 170006 170002 170020, .subN 170028 170001 170020]

/-- The whole host. -/
def initH : Stmt := .seq (block [.constN 160024 1, .constN 160029 0, .constN 160086 7])
  (.seq proH (block [.copyN 170004 160027]))

/-- The record of grade `0` and the registers of grade `0`. -/
def initR : Stmt := block [.copyN 170005 9999, .storeN 170005 170029,
  .addN 170053 170005 170020, .storeN 170053 170000,
  .addN 170053 170005 170021, .addN 170054 170005 170025, .storeN 170053 170054,
  .addN 170053 170005 170022, .storeN 170053 170003, .addN 9999 9999 170025,
  .constN 170007 0, .copyN 170008 170028, .subN 170009 170028 170020, .constN 170010 1,
  .constN 170011 1, .copyN 170012 170028, .constN 170014 0, .constN 170019 1,
  .constN 170015 0, .constN 170016 0, .constN 170035 0, .constN 170036 1]

/-- The registers written by `initR` (besides the allocator). -/
def InitRRG (r : ℕ) : Prop :=
  r = 170005 ∨ r = 170053 ∨ r = 170054 ∨ r = 170007 ∨ r = 170008 ∨ r = 170009 ∨
    r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170014 ∨ r = 170019 ∨ r = 170015 ∨
    r = 170016 ∨ r = 170035 ∨ r = 170036

section proofs

variable {P : Polygon} {W : ℕ}

theorem initA_exec {c : Config} (hw : WordsBounded W c) {S p : ℕ}
    (h00 : c.nreg 230000 = S) (hS1 : c.nmem (S + 1) = p) (hWS : S + 1 ≤ W) (hWp : p + 1 ≤ W)
    (hWn : P.n ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initA c c' k ∧ k = 14 ∧ WordsBounded W c' ∧
      c'.nreg 170020 = 1 ∧ c'.nreg 170021 = 2 ∧ c'.nreg 170022 = 3 ∧ c'.nreg 170023 = 5 ∧
      c'.nreg 170025 = 4 ∧ c'.nreg 170026 = 6 ∧ c'.nreg 170029 = 0 ∧ c'.nreg 170037 = 7 ∧
      c'.nreg 170000 = S ∧ c'.nreg 170001 = P.n ∧ c'.nreg 170002 = p ∧
      c'.nreg 170006 = p + 1 ∧ c'.nreg 170028 = P.n - 1 ∧
      (∀ r, bandOf r ≠ bUp → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold initA
  exec_block
  all_goals try (config_simp; (try simp only [h00, hS1]); omega)
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, by config_simp; exact h00,
    by config_simp, by config_simp; simp only [h00, hS1], by config_simp; simp only [h00, hS1],
    by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  unfold bandOf bUp at hr
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

theorem initH_exec {c : Config} (hw : WordsBounded W c) {A : ℕ} (hA : c.nreg ALLOC = A)
    (hn : 1 ≤ P.n) (hW : A + 7 ≤ W) (hWn : P.n ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initH c c' k ∧ k = 16 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 7 ∧ c'.nreg 170004 = A ∧ HostAt c'.nmem A (Host.whole P.n) ∧
      (∀ a, (a < A ∨ A + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ≠ bL41 → r ≠ 170004 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i24, i29, i86, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 160024 1, .constN 160029 0, .constN 160086 7]) c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160024 = 1 ∧ c1.nreg 160029 = 0 ∧ c1.nreg 160086 = 7 ∧
      (∀ r, r ≠ 160024 → r ≠ 160029 → r ≠ 160086 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, fun r a1 a2 a3 => ?_, rfl,
      rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA1 : c1.nreg ALLOC = A := by
    rw [fr1 _ (by rwo [hAl]) (by rwo [hAl]) (by rwo [hAl])]; exact hA
  obtain ⟨c2, k2, e2, hk2, hw2, A2, j27, j15, hH, hm2, fr2, hrr2, hrm2, ho2⟩ :=
    proH_exec (P := P) hw1 hA1 i24 i29 i86 hn hW hWn
  obtain ⟨c3, k3, e3, hk3, hw3, j04, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 170004 160027]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170004 = c2.nreg 160027 ∧ (∀ r, r ≠ 170004 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  refine ⟨c3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, hw3,
    by rw [fr3 _ (by rwo [hAl])]; exact A2, by rw [j04, j27], by rwx [hm3],
    fun a ha => by rw [hm3, hm2 a ha, hm1], fun r h1 h2 h3 => ?_, by rw [hrr3, hrr2, hrr1],
    by rw [hrm3, hrm2, hrm1], by rw [ho3, ho2, ho1]⟩
  have : r < 160000 ∨ 170000 ≤ r := by ufo bandOf bL41 at h1
  rw [fr3 r h2, fr2 r (by omega) (by omega) (by omega) (by omega) h3,
    fr1 r (by omega) (by omega) (by omega)]

theorem initR_exec {c : Config} (hw : WordsBounded W c) {H S D n1 : ℕ}
    (hA : c.nreg ALLOC = H) (h00 : c.nreg 170000 = S) (h03 : c.nreg 170003 = D)
    (h28 : c.nreg 170028 = n1) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (h22 : c.nreg 170022 = 3) (h25 : c.nreg 170025 = 4) (h29 : c.nreg 170029 = 0)
    (hW : H + 4 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initR c c' k ∧ k = 22 ∧ WordsBounded W c' ∧
      c'.nreg 170005 = H ∧ c'.nreg ALLOC = H + 4 ∧
      c'.nmem H = 0 ∧ c'.nmem (H + 1) = S ∧ c'.nmem (H + 2) = H + 4 ∧ c'.nmem (H + 3) = D ∧
      c'.nreg 170007 = 0 ∧ c'.nreg 170008 = n1 ∧ c'.nreg 170009 = n1 - 1 ∧
      c'.nreg 170010 = 1 ∧ c'.nreg 170011 = 1 ∧ c'.nreg 170012 = n1 ∧ c'.nreg 170014 = 0 ∧
      c'.nreg 170019 = 1 ∧ c'.nreg 170015 = 0 ∧ c'.nreg 170016 = 0 ∧ c'.nreg 170035 = 0 ∧
      c'.nreg 170036 = 1 ∧
      (∀ a, (a < H ∨ H + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ InitRRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold initR
  exec_block
  all_goals
    try (config_simp; (try simp only [hA, h00, h03, h28, h20, h21, h22, h25, h29]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp <;> (try simp only [hA, h00, h03, h28, h20, h21, h22, h25, h29,
    Machine.upd_apply]) <;> (try split_ifs) <;> first | omega | rfl)
  unfold InitRRG at h1
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

end proofs

end

end Chazelle.Core.Up
