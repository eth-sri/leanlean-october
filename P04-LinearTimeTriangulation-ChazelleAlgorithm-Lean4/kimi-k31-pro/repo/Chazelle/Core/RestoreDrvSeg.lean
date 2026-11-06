module

public import Chazelle.Core.RestoreDrvMath
set_option maxHeartbeats 2000000

/-!
# WP-E, part 10: the restoration driver — straight-line segments of a round

Execution lemmas for `headS`, `midS`, `preRegS`, the argument block of `buildS`, the handle
copy and the round counter (`head_exec`, `mid_exec`, `preReg_exec`, `bargs_exec`,
`bhandle_exec`, `incr_exec`), and for the initialisation and the output (`init_exec`,
`out_exec`).
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs

@[expose] public section

theorem head_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {H : ℕ}
    (h12 : c.nreg 80012 = H) (h21 : c.nreg 80021 = 2) (h22 : c.nreg 80022 = 3)
    (hH : H + 5 ≤ W) :
    ∃ c' k, Exec P W headS c c' k ∧ k = 10 ∧
      c'.nreg 80013 = c.nmem H ∧ c'.nreg 80014 = c.nmem (H + 2) ∧
      c'.nreg 80015 = c.nmem (H + 3) ∧ c'.nreg 80016 = c.nmem (H + 5) ∧
      c'.nreg 80017 = c.nreg ALLOC ∧ c'.nreg 80031 = c.nmem (H + 3) ∧ c'.nreg 80030 = 0 ∧
      (∀ r, (r < 80013 ∨ (80017 < r ∧ r < 80030) ∨ (80031 < r ∧ r ≠ 80036)) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold headS
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h12, h21, h22, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
    (try simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h12, h21, h22, ALLOC])

theorem mid_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W midS c c' k ∧ k = 3 ∧ c'.nreg 80018 = c.nreg 80013 ∧
      c'.nreg 80043 = c.nreg ALLOC ∧ c'.nreg 80034 = 0 ∧
      (∀ r, r ≠ 80018 → r ≠ 80043 → r ≠ 80034 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold midS
  exec_block
  · omega
  · refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ALLOC]

theorem preReg_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h : c.nreg 80016 + c.nreg 80021 ≤ W) :
    ∃ c' k, Exec P W preRegS c c' k ∧ k = 2 ∧ c'.nreg 80040 = 0 ∧
      c'.nreg 80041 = c.nreg 80016 + c.nreg 80021 ∧
      (∀ r, r ≠ 80040 → r ≠ 80041 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold preRegS
  exec_block
  · omega
  · simp (disch := omega) only [Machine.upd_other]; exact h
  · refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem bargs_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (block [.copyN 40000 80000, .copyN 40001 80017, .copyN 40002 80018]) c c' k ∧
      k = 3 ∧ c'.nreg 40000 = c.nreg 80000 ∧ c'.nreg 40001 = c.nreg 80017 ∧
      c'.nreg 40002 = c.nreg 80018 ∧
      (∀ r, r ≠ 40000 → r ≠ 40001 → r ≠ 40002 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem copy1_exec' {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (a b : ℕ) :
    ∃ c' k, Exec P W (block [.copyN a b]) c c' k ∧ k = 1 ∧ c'.nreg a = c.nreg b ∧
      (∀ r, r ≠ a → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  Gran.copy1_exec c hw a b

theorem incr_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h : c.nreg 80010 + c.nreg 80020 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 80010 80010 80020]) c c' k ∧ k = 1 ∧
      c'.nreg 80010 = c.nreg 80010 + c.nreg 80020 ∧
      (∀ r, r ≠ 80010 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · exact h
  · refine ⟨rfl, ?_, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem init_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (hW : 5 ≤ W) (h1 : c.nreg 80002 + 1 ≤ W) (h2 : c.nreg 80002 + c.nreg 80003 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 9 ∧
      c'.nreg 80020 = 1 ∧ c'.nreg 80021 = 2 ∧ c'.nreg 80022 = 3 ∧ c'.nreg 80023 = 5 ∧
      c'.nreg 80024 = 0 ∧ c'.nreg 80012 = c.nreg 80001 ∧ c'.nreg 80010 = 0 ∧
      c'.nreg 80011 = c.nreg 80002 + 1 ∧ c'.nreg 80019 = c.nreg 80002 + c.nreg 80003 ∧
      (∀ r, (r < 80010 ∨ 80025 ≤ r) → r ≠ 80012 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold initS
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

end

end Restore

end Chazelle.Core
