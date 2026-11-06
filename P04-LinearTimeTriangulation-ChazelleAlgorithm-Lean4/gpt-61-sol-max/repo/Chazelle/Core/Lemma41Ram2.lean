module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.Lemma41Ram1
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.List.GetD

/-!
# WP-J, part 7: the cover loop on the RAM

`coverS`: while `x < b`, find the greedy grade `g` and the index `q = x / 2^g` (`ascS`), copy the
table entry of chain `(g, q)` into a six-word record `[host, s, m, top, bit, NF]` at the record
pointer, and advance `x` by `2^g`. The records are those of `cover λ b a` (`coverS_exec`).

Registers: `160014` count, `160015` record pointer, `160022` row table base `T`, `160027` host
handle; the table entry of chain `(g, i)` is at `m (T + g) + 3 i` (descriptor, NF).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs

@[expose] public section

/-- The address computation: descriptor `160017`, NF handle `160018`, entry `160016`. -/
def entB : Stmt := block [.addN 160016 160022 160012, .loadN 160016 160016,
  .addN 160016 160016 160013, .addN 160016 160016 160013, .addN 160016 160016 160013,
  .loadN 160017 160016, .addN 160018 160016 160024, .loadN 160018 160018]

/-- The record stores. -/
def recB : Stmt := block [.storeN 160015 160027,
  .addN 160019 160015 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .storeN 160019 160018]

/-- The advance. -/
def advB : Stmt := block [.addN 160015 160019 160024, .addN 160014 160014 160024,
  .addN 160016 160021 160012, .loadN 160016 160016, .addN 160010 160010 160016]

/-- One piece. -/
def coverBody : Stmt := .seq ascS (.seq entB (.seq recB advB))

/-- **The cover loop.** -/
def coverS : Stmt := .whileLtN 160010 160011 coverBody

/-- The registers written by `coverS`. -/
def CovRG (r : ℕ) : Prop := AscRG r ∨ r = 160010 ∨ r = 160014 ∨ r = 160015

/-- The record of piece `q` at slot `k`: host handle, the four descriptor words of the table
entry of chain `(q.1, q.2 / 2^q.1)`, its NF handle. -/
def RecAt (m m0 : ℕ → ℕ) (R hp T : ℕ) (q : ℕ × ℕ) (k : ℕ) : Prop :=
  m (R + 6 * k) = hp ∧
    (∀ j, 1 ≤ j → j ≤ 4 → m (R + 6 * k + j) =
      m0 (m0 (m0 (T + q.1) + 3 * (q.2 / 2 ^ q.1)) + j)) ∧
    m (R + 6 * k + 5) = m0 (m0 (T + q.1) + 3 * (q.2 / 2 ^ q.1) + 1)

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- The entry of chain `(g, q)`. -/
theorem entB_exec {c : Config} (hw : WordsBounded W c) {T g q : ℕ}
    (h22 : c.nreg 160022 = T) (h12 : c.nreg 160012 = g) (h13 : c.nreg 160013 = q)
    (h24 : c.nreg 160024 = 1)
    (hW1 : T + g ≤ W) (hW2 : c.nmem (T + g) + 3 * q + 1 ≤ W) :
    ∃ c' k, Exec P W entB c c' k ∧ k = 8 ∧ WordsBounded W c' ∧
      c'.nreg 160017 = c.nmem (c.nmem (T + g) + 3 * q) ∧
      c'.nreg 160018 = c.nmem (c.nmem (T + g) + 3 * q + 1) ∧
      (∀ r, r ≠ 160016 → r ≠ 160017 → r ≠ 160018 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold entB
  exec_block
  all_goals try (config_simp; simp only [h22, h12, h13, h24]; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [h22, h12, h13]
    rw [show c.nmem (T + g) + q + q + q = c.nmem (T + g) + 3 * q by ring]
  · config_simp; simp only [h22, h12, h13, h24]
    rw [show c.nmem (T + g) + q + q + q + 1 = c.nmem (T + g) + 3 * q + 1 by ring]
  · simp only [Machine.upd_apply]
    split_ifs <;> first | omega

set_option maxHeartbeats 16000000 in
/-- The record stores. -/
theorem recB_exec {c : Config} (hw : WordsBounded W c) {rp d nf hp : ℕ}
    (h15 : c.nreg 160015 = rp) (h17 : c.nreg 160017 = d) (h18 : c.nreg 160018 = nf)
    (h27 : c.nreg 160027 = hp) (h24 : c.nreg 160024 = 1)
    (hd : d + 4 < rp) (hW : rp + 6 ≤ W) :
    ∃ c' k, Exec P W recB c c' k ∧ k = 19 ∧ WordsBounded W c' ∧
      c'.nmem rp = hp ∧ (∀ j, 1 ≤ j → j ≤ 4 → c'.nmem (rp + j) = c.nmem (d + j)) ∧
      c'.nmem (rp + 5) = nf ∧ (∀ a, (a < rp ∨ rp + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 160019 = rp + 5 ∧
      (∀ r, r ≠ 160016 → r ≠ 160017 → r ≠ 160019 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold recB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, ?_, fun j hj1 hj4 => ?_, ?_, fun a ha => ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl,
    rfl⟩
  · grind [Machine.upd_apply]
  · grind [Machine.upd_apply]
  · ram_simp <;> omega_nf
  · config_simp; simp only [h15, h17, h18, h27, h24, Machine.upd_apply]
    grind
  all_goals (ram_simp <;> omega_nf)

set_option maxHeartbeats 4000000 in
/-- The advance. -/
theorem advB_exec {c : Config} (hw : WordsBounded W c) {rp cnt PW g x : ℕ}
    (h19 : c.nreg 160019 = rp) (h14 : c.nreg 160014 = cnt) (h21 : c.nreg 160021 = PW)
    (h12 : c.nreg 160012 = g) (h10 : c.nreg 160010 = x) (h24 : c.nreg 160024 = 1)
    (hp : c.nmem (PW + g) = 2 ^ g) (hW1 : rp + 1 ≤ W) (hW2 : cnt + 1 ≤ W) (hW3 : PW + g ≤ W)
    (hW4 : x + 2 ^ g ≤ W) :
    ∃ c' k, Exec P W advB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160015 = rp + 1 ∧ c'.nreg 160014 = cnt + 1 ∧ c'.nreg 160010 = x + 2 ^ g ∧
      (∀ r, r ≠ 160015 → r ≠ 160014 → r ≠ 160016 → r ≠ 160010 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold advB
  exec_block
  all_goals try (config_simp; simp only [h19, h14, h21, h12, h10, h24, hp]; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [h19, h24]
  · config_simp; simp only [h14, h24]
  · config_simp; simp only [h21, h12, h10, hp]
  · simp only [Machine.upd_apply]
    split_ifs <;> first | omega

end proofs

end

end Chazelle.Core.L41
