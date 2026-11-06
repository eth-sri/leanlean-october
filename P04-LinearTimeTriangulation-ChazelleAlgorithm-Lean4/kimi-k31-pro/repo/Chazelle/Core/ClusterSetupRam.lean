module

public import Chazelle.Core.ClusterSetup
public import Mathlib.Tactic.IntervalCases
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 8000000

/-!
# WP-I, part 43: the setup program

`setupStmt` computes the global values of `GV` in the global registers (see
`ClusterSetup.lean`) without touching memory; `setupStmt_exec`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- Copy the inputs, the constants, `N`, the bases of the input arrays and the allocator. -/
def setupA : Stmt := block [.copyN 130010 130000, .copyN 130011 130001, .copyN 130012 130002,
  .copyN 130013 130003, .constN 130001 1, .constN 130009 0, .addN 130014 130012 130012,
  .loadN 130021 130010, .addN 130090 130010 130001, .loadN 130022 130090,
  .addN 130090 130090 130001, .loadN 130023 130090, .copyN 130020 9999]

/-- `k' := min k μ`. -/
def kminS : Stmt := .ifLtN 130013 130011 (.instr (.copyN 130015 130013))
  (.instr (.copyN 130015 130011))

/-- One step of `s := min (k' k') μ`. -/
def sBody : Stmt := .seq (.instr (.addN 130016 130016 130015))
  (.seq (.ifLtN 130011 130016 (.instr (.copyN 130016 130011)) .skip)
    (.instr (.addN 130091 130091 130001)))

/-- `s := min (k' k') μ` by clamped additions. -/
def sS : Stmt := .seq (block [.constN 130016 0, .constN 130091 0]) (.whileLtN 130091 130015 sBody)

/-- One doubling. -/
def LBody : Stmt := block [.addN 130018 130018 130018, .addN 130017 130017 130001]

/-- `L := clog₂ (N + μ + 1)`, `P := 2 ^ L`. -/
def LS : Stmt := .seq (block [.constN 130017 0, .constN 130018 1, .addN 130092 130014 130011,
  .addN 130092 130092 130001]) (.whileLtN 130018 130092 LBody)

/-- `U := N + μ + P + 3`. -/
def UB : Stmt := block [.addN 130019 130014 130011, .addN 130019 130019 130018,
  .constN 130093 3, .addN 130019 130019 130093]

/-- The slot bases. -/
def basesB : Stmt := block [
  .copyN 130030 130020,
  .addN 130031 130030 130019,
  .addN 130032 130031 130019,
  .addN 130033 130032 130019,
  .addN 130034 130033 130019,
  .addN 130035 130034 130019,
  .addN 130036 130035 130019,
  .addN 130037 130036 130019,
  .addN 130038 130037 130019,
  .addN 130039 130038 130019,
  .addN 130040 130039 130019,
  .addN 130041 130040 130019,
  .addN 130042 130041 130019,
  .addN 130043 130042 130019,
  .addN 130044 130043 130019,
  .addN 130045 130044 130019,
  .addN 130046 130045 130019,
  .addN 130047 130046 130019,
  .addN 130048 130047 130019,
  .addN 130049 130048 130019,
  .addN 130050 130049 130019,
  .addN 130051 130050 130019,
  .addN 130052 130051 130019,
  .addN 130053 130052 130019,
  .addN 130054 130053 130019,
  .addN 130055 130054 130019,
  .addN 130056 130055 130019,
  .addN 130057 130056 130019,
  .addN 130058 130057 130019,
  .addN 130059 130058 130019,
  .addN 130060 130059 130019,
  .addN 130061 130060 130019,
  .addN 130062 130061 130019,
  .addN 130063 130062 130019,
  .addN 130064 130063 130019,
  .addN 130065 130064 130019,
  .addN 130066 130065 130019,
  .addN 130067 130066 130019,
  .addN 130068 130067 130019,
  .addN 130069 130068 130019,
  .addN 130070 130069 130019,
  .addN 130071 130070 130019,
  .addN 130072 130071 130019,
  .addN 130073 130072 130019,
  .addN 130074 130073 130019,
  .addN 130075 130074 130019,
  .addN 130076 130075 130019,
  .addN 130077 130076 130019,
  .addN 130078 130077 130019,
  .addN 130079 130078 130019,
  .addN 130080 130079 130019,
  .addN 130081 130080 130019,
  .addN 130082 130081 130019,
  .addN 130083 130082 130019,
  .addN 130084 130083 130019]

/-- One step of `L U`. -/
def LUBody : Stmt := block [.addN 130026 130026 130019, .addN 130094 130094 130001]

/-- `L U` by repeated addition. -/
def LUS : Stmt := .seq (block [.constN 130026 0, .constN 130094 0]) (.whileLtN 130094 130017 LUBody)

/-- The tables. -/
def endB : Stmt := block [.addN 130085 130084 130026, .addN 130086 130085 130026]

/-- **The setup.** -/
def setupStmt : Stmt := .seq setupA (.seq kminS (.seq sS (.seq LS (.seq UB (.seq basesB
  (.seq LUS endB))))))

/-- The registers written by the setup. -/
def SetRG (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130010 ≤ r ∧ r ≤ 130099)

section proofs

variable {P : Polygon} {W : ℕ}

theorem setupA_exec {c : Config} (hw : WordsBounded W c) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hE : c.nreg 130002 + c.nreg 130002 ≤ W) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W setupA c c' k ∧ k = 13 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130010 = c.nreg 130000 ∧ c'.nreg 130011 = c.nreg 130001 ∧
      c'.nreg 130012 = c.nreg 130002 ∧ c'.nreg 130013 = c.nreg 130003 ∧
      c'.nreg 130001 = 1 ∧ c'.nreg 130009 = 0 ∧
      c'.nreg 130014 = 2 * c.nreg 130002 ∧ c'.nreg 130020 = c.nreg 9999 ∧
      c'.nreg 130021 = c.nmem (c.nreg 130000) ∧ c'.nreg 130022 = c.nmem (c.nreg 130000 + 1) ∧
      c'.nreg 130023 = c.nmem (c.nreg 130000 + 2) ∧
      (∀ r, ¬ SetRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold setupA
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  all_goals try (config_simp; done)
  all_goals try (config_simp; omega)
  unfold SetRG at hr
  simp
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

theorem kminS_exec {c : Config} (hw : WordsBounded W c) :
    ∃ c' k, Exec P W kminS c c' k ∧ k ≤ 3 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130015 = min (c.nreg 130013) (c.nreg 130011) ∧
      (∀ r, r ≠ 130015 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold kminS
  by_cases h : c.nreg 130013 < c.nreg 130011
  · have e := Exec.copyN (P := P) hw 130015 130013
    refine ⟨_, 1 + 1, .ifLtN_true h e, by omega, e.wb_right, rfl, ?_, fun r hr => ?_, rfl, rfl,
      rfl⟩
    · sio only [Machine.upd_same]
    · simp [Machine.upd_other _ _ _ hr]
  · have e := Exec.copyN (P := P) hw 130015 130011
    refine ⟨_, 1 + 2, .ifLtN_false h e, by omega, e.wb_right, rfl, ?_, fun r hr => ?_, rfl, rfl,
      rfl⟩
    · sio only [Machine.upd_same]
    · simp [Machine.upd_other _ _ _ hr]

/-- One clamped addition. -/
theorem sBody_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {j a mu : ℕ} (hj : c.nreg 130091 = j) (hacc : c.nreg 130016 = min (j * a) mu)
    (ha : c.nreg 130015 = a) (hmu : c.nreg 130011 = mu) (hW : mu + a ≤ W) (hjW : j + 1 ≤ W) :
    ∃ c' k, Exec P W sBody c c' k ∧ k ≤ 5 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130091 = j + 1 ∧ c'.nreg 130016 = min ((j + 1) * a) mu ∧
      (∀ r, r ≠ 130016 → r ≠ 130091 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : min (j * a) mu + a ≤ W := by have := min_le_right (j * a) mu; omega
  have e1 := Exec.addN (P := P) hw 130016 130016 130015 (by rwx [hacc, ha])
  set c1 := { c with nreg := upd c.nreg 130016 (c.nreg 130016 + c.nreg 130015) }
  have hsa : (j + 1) * a = j * a + a := by ring
  by_cases h : c1.nreg 130011 < c1.nreg 130016
  · have e2 := Exec.copyN (P := P) e1.wb_right 130016 130011
    set c2 := { c1 with nreg := upd c1.nreg 130016 (c1.nreg 130011) }
    have e3 := Exec.addN (P := P) e2.wb_right 130091 130091 130001 (by
      simp [c2, c1, Machine.upd_other _ _ _ (show (130091 : ℕ) ≠ 130016 by omega),
        Machine.upd_other _ _ _ (show (130001 : ℕ) ≠ 130016 by omega), hj, hone]; exact hjW)
    refine ⟨_, 1 + ((1 + 1) + 1), .seq e1 (.seq (.ifLtN_true h e2) e3), by omega, e3.wb_right,
      rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp [c2, c1, hj, hone]
    · simp [c1, c2, Machine.upd_same, Machine.upd_other _ _ _
        (show (130016 : ℕ) ≠ 130091 by omega), Machine.upd_other _ _ _
        (show (130011 : ℕ) ≠ 130016 by omega)] at h ⊢
      rw [hmu] at h ⊢; rw [hacc, ha] at h
      rw [hsa]
      have := min_le_right (j * a) mu
      rcases le_total (j * a) mu with h' | h'
      · rwo [min_eq_left h'] at h
      · rwo [min_eq_right h'] at h
    · simp [c1, c2, Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  · have e3 := Exec.addN (P := P) e1.wb_right 130091 130091 130001 (by
      simp [c1, Machine.upd_other _ _ _ (show (130091 : ℕ) ≠ 130016 by omega),
        Machine.upd_other _ _ _ (show (130001 : ℕ) ≠ 130016 by omega), hj, hone]; exact hjW)
    refine ⟨_, 1 + ((0 + 2) + 1), .seq e1 (.seq (.ifLtN_false h (.skip e1.wb_right)) e3),
      by omega, e3.wb_right, rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp [c1, hj, hone]
    · simp [c1, Machine.upd_same, Machine.upd_other _ _ _
        (show (130016 : ℕ) ≠ 130091 by omega), Machine.upd_other _ _ _
        (show (130011 : ℕ) ≠ 130016 by omega)] at h ⊢
      rw [hmu, hacc, ha] at h
      rw [hacc, ha, hsa]
      rcases le_total (j * a) mu with h' | h'
      · rw [min_eq_left h'] at h ⊢; rw [min_eq_left (by omega)]
      · rwo [min_eq_right h'] at h ⊢
    · simp [c1, Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]

/-- `s := min (a a) μ`. -/
theorem sS_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {a mu : ℕ}
    (ha : c.nreg 130015 = a) (hmu : c.nreg 130011 = mu) (hW : mu + a + 1 ≤ W) :
    ∃ c' k, Exec P W sS c c' k ∧ k ≤ 7 * a + 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130016 = min (a * a) mu ∧
      (∀ r, r ≠ 130016 → r ≠ 130091 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h16, h91, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W (block [.constN 130016 0, .constN 130091 0]) c c1 k1 ∧ k1 = 2 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130016 = 0 ∧ c1.nreg 130091 = 0 ∧
        (∀ r, r ≠ 130016 → r ≠ 130091 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  obtain ⟨c', k, e, hk, hw', hi', hn', h16', hfr', hm', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130091) (rn := 130015) (body := sBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130091 = j ∧ c'.nreg 130015 = a ∧
      c'.nreg 130016 = min (j * a) mu ∧
      (∀ r, r ≠ 130016 → r ≠ 130091 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    a 5 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, ha2, hacc2, hfr2, hm2, hrr2, hrm2, ho2⟩ => by
      obtain ⟨c3, k3, e3, hk3, hw3, hm3, hi3, hacc3, hfr3, hrr3, hrm3, ho3⟩ :=
        sBody_exec (P := P) hw2 ((hfr2 _ (by omega) (by omega)).trans hone) hi2 hacc2 ha2
          ((hfr2 _ (by omega) (by omega)).trans hmu) (by omega) (by omega)
      refine ⟨c3, k3, e3, hk3, hw3, hi3, by rwx [hfr3 _ (by omega) (by omega)], hacc3,
        fun r h1 h2 => (hfr3 r h1 h2).trans (hfr2 r h1 h2), hm3.trans hm2, hrr3.trans hrr2,
        hrm3.trans hrm2, ho3.trans ho2⟩)
    (j₀ := 0) ⟨hw1, h91, by rwx [hr1 _ (by omega) (by omega)], by rws [h16],
      hr1, hm1, hrr1, hrm1, ho1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hm', h16', hfr', hrr', hrm', ho'⟩

/-- `L := clog₂ x`, `P := 2 ^ L` for `x = N + μ + 1`. -/
theorem LS_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {x : ℕ}
    (hx : c.nreg 130014 + c.nreg 130011 + 1 = x) (hW : 2 * x ≤ W) :
    ∃ c' k, Exec P W LS c c' k ∧ k ≤ 4 * Nat.clog 2 x + 6 ∧ WordsBounded W c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 130017 = Nat.clog 2 x ∧ c'.nreg 130018 = 2 ^ Nat.clog 2 x ∧
      (∀ r, r ≠ 130017 → r ≠ 130018 → r ≠ 130092 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold LS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h17, h18, h92, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W (block [.constN 130017 0, .constN 130018 1, .addN 130092 130014 130011,
        .addN 130092 130092 130001]) c c1 k1 ∧ k1 = 4 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130017 = 0 ∧ c1.nreg 130018 = 1 ∧
        c1.nreg 130092 = x ∧
        (∀ r, r ≠ 130017 → r ≠ 130018 → r ≠ 130092 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ‹_›, rfl, by config_simp, by config_simp, by cso,
      fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
    simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2,
      Machine.upd_other _ _ _ h3]
  have h2 : (1 : ℕ) < 2 := by omega
  obtain ⟨c', k, e, ⟨hw', j, hj, hp', hjx, hfr', hm', hrr', hrm', ho'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130018) (b := 130092) (body := LBody)
    (fun c' => WordsBounded W c' ∧ ∃ j, c'.nreg 130017 = j ∧ c'.nreg 130018 = 2 ^ j ∧
      j ≤ Nat.clog 2 x ∧
      (∀ r, r ≠ 130017 → r ≠ 130018 → c'.nreg r = c1.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun c' => 4 * (Nat.clog 2 x - c'.nreg 130017)) (fun c' h => h.1)
    (fun c2 ⟨hw2, j, hj2, hp2, hjx2, hfr2, hm2, hrr2, hrm2, ho2⟩ htest => by
      have hx2 : c2.nreg 130092 = x := (hfr2 _ (by omega) (by omega)).trans h92
      rw [hp2, hx2] at htest
      have hjc : j < Nat.clog 2 x := (Nat.lt_clog_iff_pow_lt h2).mpr htest
      have hone2 : c2.nreg 130001 = 1 := (hfr2 _ (by omega) (by omega)).trans
        ((hr1 _ (by omega) (by omega) (by omega)).trans hone)
      have hj2p : j < 2 ^ j := Nat.lt_two_pow_self
      unfold LBody
      exec_block
      · rwo [hp2]
      · config_simp; rwo [hj2, hone2]
      · refine ⟨⟨‹_›, j + 1, by config_simp; rw [hj2, hone2], by config_simp; rwring [hp2],
          by omega, fun r h1 h2 => ?_, hm2, hrr2, hrm2, ho2⟩, ?_⟩
        · simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
          exact hfr2 r h1 h2
        · config_simp; rwo [hj2, hone2])
    ⟨hw1, 0, h17, by rwr [h18], Nat.zero_le _, fun _ _ _ => rfl, hm1, hrr1, hrm1, ho1⟩
  have hx' : c'.nreg 130092 = x := (hfr' _ (by omega) (by omega)).trans h92
  rw [hp', hx'] at htest
  have hjx' : Nat.clog 2 x ≤ j := (Nat.clog_le_iff_le_pow h2).mpr (by omega)
  have hjeq : j = Nat.clog 2 x := le_antisymm hjx hjx'
  subst hjeq
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hm', hj, hp', fun r h1 h2 h3 => ?_, hrr', hrm', ho'⟩
  · sio only [h17] at hk
  · rw [hfr' r h1 h2, hr1 r h1 h2 h3]

/-- `U`. -/
theorem UB_exec {c : Config} (hw : WordsBounded W c)
    (hW : c.nreg 130014 + c.nreg 130011 + c.nreg 130018 + 3 ≤ W) :
    ∃ c' k, Exec P W UB c c' k ∧ k = 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130019 = c.nreg 130014 + c.nreg 130011 + c.nreg 130018 + 3 ∧
      (∀ r, r ≠ 130019 → r ≠ 130093 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold UB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, rfl, by config_simp; try omega, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]

/-- `L U`. -/
theorem LUS_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {L U : ℕ}
    (hL : c.nreg 130017 = L) (hU : c.nreg 130019 = U) (hW : L * U + L + 1 ≤ W) :
    ∃ c' k, Exec P W LUS c c' k ∧ k ≤ 4 * L + 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130026 = L * U ∧
      (∀ r, r ≠ 130026 → r ≠ 130094 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold LUS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h26, h94, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W (block [.constN 130026 0, .constN 130094 0]) c c1 k1 ∧ k1 = 2 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130026 = 0 ∧ c1.nreg 130094 = 0 ∧
        (∀ r, r ≠ 130026 → r ≠ 130094 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  obtain ⟨c', k, e, hk, hw', hi', hn', h26', hfr', hm', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130094) (rn := 130017) (body := LUBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130094 = j ∧ c'.nreg 130017 = L ∧
      c'.nreg 130026 = j * U ∧
      (∀ r, r ≠ 130026 → r ≠ 130094 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    L 2 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hL2, hacc2, hfr2, hm2, hrr2, hrm2, ho2⟩ => by
      have hU2 : c2.nreg 130019 = U := (hfr2 _ (by omega) (by omega)).trans hU
      have hone2 : c2.nreg 130001 = 1 := (hfr2 _ (by omega) (by omega)).trans hone
      have hjU : (j + 1) * U ≤ L * U := Nat.mul_le_mul_right _ (by omega)
      unfold LUBody
      exec_block
      · rw [hacc2, hU2]; rwo [Nat.succ_mul] at hjU
      · config_simp; rwo [hi2, hone2]
      · refine ⟨le_refl _, ‹_›, by config_simp; rw [hi2, hone2], by config_simp; exact hL2,
          by config_simp; rwring [hacc2, hU2], fun r h1 h2 => ?_, hm2, hrr2, hrm2, ho2⟩
        simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
        exact hfr2 r h1 h2)
    (j₀ := 0) ⟨hw1, h94, by rwx [hr1 _ (by omega) (by omega)], by rws [h26],
      hr1, hm1, hrr1, hrm1, ho1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hm', h26', hfr', hrr', hrm', ho'⟩

/-- The table bases. -/
theorem endB_exec {c : Config} (hw : WordsBounded W c)
    (hW : c.nreg 130084 + c.nreg 130026 + c.nreg 130026 ≤ W) :
    ∃ c' k, Exec P W endB c c' k ∧ k = 2 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130085 = c.nreg 130084 + c.nreg 130026 ∧
      c'.nreg 130086 = c.nreg 130084 + c.nreg 130026 + c.nreg 130026 ∧
      (∀ r, r ≠ 130085 → r ≠ 130086 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold endB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]

/-- The slot bases. -/
theorem basesB_exec {c : Config} (hw : WordsBounded W c) {A0 U : ℕ} (hA : c.nreg 130020 = A0)
    (hU : c.nreg 130019 = U) (hW : A0 + 54 * U ≤ W) :
    ∃ c' k, Exec P W basesB c c' k ∧ k = 55 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      (∀ j, j ≤ 54 → c'.nreg (130030 + j) = A0 + j * U) ∧
      (∀ r, ¬ (130030 ≤ r ∧ r ≤ 130084) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold basesB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, rfl, fun j hj => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · interval_cases j <;> (config_simp; omega)
  · simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

/-- The global values read from the entry configuration. -/
def gOf (c : Config) : GV := ⟨c.nreg 130000, c.nreg 130001, c.nreg 130002, c.nreg 130003,
  c.nreg 9999, c.nmem (c.nreg 130000), c.nmem (c.nreg 130000 + 1), c.nmem (c.nreg 130000 + 2)⟩

theorem GV.two_pow_L (g : GV) : g.N + g.μ + 1 ≤ 2 ^ g.L :=
  Nat.le_pow_clog (by omega) _

theorem GV.U_eq (g : GV) : g.U = g.N + g.μ + 2 ^ g.L + 3 := rfl

theorem GV.U_ge (g : GV) : g.N + g.μ + 3 ≤ g.U := by
  rw [GV.U_eq]; generalize 2 ^ g.L = p; omega

theorem GV.P_le_U (g : GV) : 2 ^ g.L ≤ g.U := by
  rw [GV.U_eq]; generalize 2 ^ g.L = p; omega

theorem GV.END_eq (g : GV) : g.END = g.A0 + 54 * g.U + 2 * (g.L * g.U) := rfl

theorem GV.base_eq (g : GV) (j : ℕ) : g.base j = g.A0 + j * g.U := rfl

theorem GV.L_le_U (g : GV) : g.L ≤ g.U := by
  have := Nat.lt_two_pow_self (n := g.L)
  ufo GV.U

/-- **The setup.** -/
theorem setupStmt_exec {c : Config} (hw : WordsBounded W c) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hEND : (gOf c).END ≤ W) :
    ∃ c' k, Exec P W setupStmt c c' k ∧ k ≤ 7 * (gOf c).μ + 8 * (gOf c).L + 100 ∧
      WordsBounded W c' ∧ c'.nmem = c.nmem ∧ GR (gOf c) c' ∧
      (∀ r, ¬ SetRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set g := gOf c with hg
  have hP := g.two_pow_L
  have hLU := g.L_le_U
  have hLUm : g.L * g.U ≥ g.L := Nat.le_mul_of_pos_right _ (by ufo GV.U)
  have hEND' : g.A0 + 54 * g.U + 2 * (g.L * g.U) ≤ W := hEND
  have hUdef : g.U = g.N + g.μ + 2 ^ g.L + 3 := rfl
  have hNdef : g.N = 2 * g.E := rfl
  have hk' : g.k' ≤ g.μ := min_le_right _ _
  have hk'def : g.k' = min g.k g.μ := rfl
  have hsdef : g.s = min (g.k' * g.k') g.μ := rfl
  have hLdef : g.L = Nat.clog 2 (g.N + g.μ + 1) := rfl
  have e0 : g.B = c.nreg 130000 := rfl
  have e1 : g.μ = c.nreg 130001 := rfl
  have e2 : g.E = c.nreg 130002 := rfl
  have e3 : g.k = c.nreg 130003 := rfl
  have e4 : g.A0 = c.nreg 9999 := rfl
  -- inputs
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, r10, r11, r12, r13, r01, r09, r14, r20, r21, r22, r23, hf1,
    hrr1, hrm1, ho1⟩ := setupA_exec (P := P) hw hB2 (by omega) (by omega)
  -- k'
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, r15, hf2, hrr2, hrm2, ho2⟩ := kminS_exec (P := P) hw1
  have q2 : ∀ r, r ≠ 130015 → c2.nreg r = c1.nreg r := hf2
  -- s
  obtain ⟨c3, k3, x3, hk3, hw3, hm3, r16, hf3, hrr3, hrm3, ho3⟩ := sS_exec (P := P) hw2
    (by rwx [q2 _ (by omega)]) (a := g.k') (mu := g.μ)
    (by rwr [r15, r13, r11]) (by rwr [q2 _ (by omega), r11]) (by omega)
  -- L
  obtain ⟨c4, k4, x4, hk4, hw4, hm4, r17, r18, hf4, hrr4, hrm4, ho4⟩ := LS_exec (P := P) hw3
    (by rwx [hf3 _ (by omega) (by omega), q2 _ (by omega)]) (x := g.N + g.μ + 1)
    (by rw [hf3 _ (by omega) (by omega), hf3 _ (by omega) (by omega), q2 _ (by omega),
      q2 _ (by omega), r14, r11]; rfl) (by omega)
  rw [← hLdef] at r17 r18 hk4
  -- U
  obtain ⟨c5, k5, x5, hk5, hw5, hm5, r19, hf5, hrr5, hrm5, ho5⟩ := UB_exec (P := P) hw4
    (by rw [r18, hf4 _ (by omega) (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega),
      hf3 _ (by omega) (by omega), hf3 _ (by omega) (by omega), q2 _ (by omega), q2 _ (by omega),
      r14, r11]; omega)
  have hU5 : c5.nreg 130019 = g.U := by
    rw [r19, hf4 _ (by omega) (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega),
      hf3 _ (by omega) (by omega), hf3 _ (by omega) (by omega), q2 _ (by omega), q2 _ (by omega),
      r14, r11, r18]; rfl
  -- the bases
  have hA5 : c5.nreg 130020 = g.A0 := by
    rw [hf5 _ (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega),
      hf3 _ (by omega) (by omega), q2 _ (by omega), r20]; rfl
  obtain ⟨c6, k6, x6, hk6, hw6, hm6, rb6, hf6, hrr6, hrm6, ho6⟩ := basesB_exec (P := P) hw5 hA5
    hU5 (by omega)
  -- L U
  obtain ⟨c7, k7, x7, hk7, hw7, hm7, r26, hf7, hrr7, hrm7, ho7⟩ := LUS_exec (P := P) hw6
    (L := g.L) (U := g.U)
    (by rw [hf6 _ (by omega), hf5 _ (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega),
      hf3 _ (by omega) (by omega), q2 _ (by omega)]; exact r01)
    (by rwx [hf6 _ (by omega), hf5 _ (by omega) (by omega)])
    (by rwx [hf6 _ (by omega)]) (by omega)
  obtain ⟨c8, k8, x8, hk8, hw8, hm8, r85, r86, hf8, hrr8, hrm8, ho8⟩ := endB_exec (P := P) hw7
    (by rwo [hf7 _ (by omega) (by omega), rb6 54 le_rfl, r26])
  -- the registers at the end
  have back : ∀ r, r ≠ 130085 → r ≠ 130086 → r ≠ 130026 → r ≠ 130094 →
      ¬ (130030 ≤ r ∧ r ≤ 130084) → r ≠ 130019 → r ≠ 130093 → r ≠ 130017 → r ≠ 130018 →
      r ≠ 130092 → r ≠ 130016 → r ≠ 130091 → r ≠ 130015 → c8.nreg r = c1.nreg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    rw [hf8 r a1 a2, hf7 r a3 a4, hf6 r a5, hf5 r a6 a7, hf4 r a8 a9 a10, hf3 r a11 a12, q2 r a13]
  refine ⟨c8, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + k8)))))),
    .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 (.seq x6 (.seq x7 x8)))))), ?_, hw8, ?_, ?_,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · have : g.k' ≤ g.μ := hk'
    omega
  · rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_,
      ?_, ?_⟩
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r01
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r09
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r10
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r11
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r12
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r13
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r14
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega),
        hf5 _ (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega),
        hf3 _ (by omega) (by omega), r15, r13, r11]; rfl
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega),
        hf5 _ (by omega) (by omega), hf4 _ (by omega) (by omega) (by omega), r16]; rfl
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega),
        hf5 _ (by omega) (by omega), r17]
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega),
        hf5 _ (by omega) (by omega), r18]
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega)]
      exact hU5
    · rw [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), hf6 _ (by omega)]
      exact hA5
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r21
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r22
    · rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r23
    · rw [hf8 _ (by omega) (by omega), r26]
    · rwr [hf8 _ (by omega) (by omega), hf7 _ (by omega) (by omega), rb6 j hj]
    · rw [r85, hf7 _ (by omega) (by omega), rb6 54 le_rfl, r26]
    · rw [r86, hf7 _ (by omega) (by omega), rb6 54 le_rfl, r26]; ufring GV.END
  · unfold SetRG at hr
    rw [back _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hf1 r (by ufo SetRG)
  · rw [hrr8, hrr7, hrr6, hrr5, hrr4, hrr3, hrr2, hrr1]
  · rw [hrm8, hrm7, hrm6, hrm5, hrm4, hrm3, hrm2, hrm1]
  · rw [ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1]

end proofs

end

end Chazelle.Core.Cluster
