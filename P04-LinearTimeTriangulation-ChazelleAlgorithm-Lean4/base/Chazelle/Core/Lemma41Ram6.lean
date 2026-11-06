module

public import Chazelle.Core.Lemma41Node
public import Chazelle.Core.Lemma41Ram5

/-!
# WP-J, part 14: the straight-line pieces of one merge step

One merge step of a level reads two consecutive entries `[d₁, f₁], [d₂, f₂]` of the level array at
the pointer `160065`, reserves five words for the descriptor of the union (`preB`), writes it
(`descS`), loads the merge registers (`setupB`), merges, and appends a cell `[TD, NF, prev]` at the
allocator linking back to the previous cell (`postB`).

Registers: `160035`/`160090` `d₁`/`f₁`, `160036`/`160091` `d₂`/`f₂`, `160037` `TD`, `160092` the new
cell, `160093` scratch, `160062` index, `160063` last cell, `160064` count of the next level,
`160065` pointer; `160033` `γ₀`, `160034` target, `160000` the context handle; constants
`160024 = 1`, `160080 = 2`, `160081 = 5`, `160083 = 3`, `160084 = 4`.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs

@[expose] public section

/-- Load the two entries; reserve the descriptor of the union. -/
def preB : Stmt := block [.loadN 160035 160065,
  .addN 160093 160065 160024, .loadN 160090 160093,
  .addN 160093 160093 160024, .loadN 160036 160093,
  .addN 160093 160093 160024, .loadN 160091 160093,
  .copyN 160037 9999, .addN 9999 9999 160081]

/-- The merge registers. -/
def setupB : Stmt := block [.copyN 100000 160035, .copyN 100001 160036, .copyN 100002 160037,
  .copyN 100003 160090, .copyN 100004 160091, .copyN 100005 160033, .copyN 100006 160034,
  .copyN 100007 160084, .copyN 100009 160000]

/-- The new cell `[TD, NF, prev]` and the advance. -/
def postB : Stmt := block [.copyN 160092 9999, .storeN 160092 160037,
  .addN 160093 160092 160024, .storeN 160093 100008,
  .addN 160093 160093 160024, .storeN 160093 160063,
  .copyN 160063 160092, .addN 9999 9999 160083,
  .addN 160065 160065 160084, .addN 160062 160062 160080, .addN 160064 160064 160024]

theorem rd_merge (c : Config) (i : ℕ) : rd c bMerge i = c.nreg (100000 + i) := rfl

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem preB_exec {c : Config} (hw : WordsBounded W c) {ptr A : ℕ}
    (h65 : c.nreg 160065 = ptr) (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5)
    (hA : c.nreg ALLOC = A) (hW : ptr + 3 ≤ W) (hWA : A + 5 ≤ W) :
    ∃ c' k, Exec P W preB c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160035 = c.nmem ptr ∧ c'.nreg 160090 = c.nmem (ptr + 1) ∧
      c'.nreg 160036 = c.nmem (ptr + 2) ∧ c'.nreg 160091 = c.nmem (ptr + 3) ∧
      c'.nreg 160037 = A ∧ c'.nreg ALLOC = A + 5 ∧
      (∀ r, r ≠ 160035 → r ≠ 160036 → r ≠ 160037 → r ≠ 160090 → r ≠ 160091 → r ≠ 160093 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold preB
  exec_block
  all_goals try (config_simp; (try simp only [h65, h24, h81, hA]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [h65]
  · config_simp; simp only [h65, h24]
  · config_simp; simp only [h65, h24]
  · config_simp; simp only [h65, h24]
  · config_simp; simp only [hA]
  · config_simp; simp only [hA, h81]
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem setupB_exec {c : Config} (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setupB c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      rd c' bMerge 0 = c.nreg 160035 ∧ rd c' bMerge 1 = c.nreg 160036 ∧
      rd c' bMerge 2 = c.nreg 160037 ∧ rd c' bMerge 3 = c.nreg 160090 ∧
      rd c' bMerge 4 = c.nreg 160091 ∧ rd c' bMerge 5 = c.nreg 160033 ∧
      rd c' bMerge 6 = c.nreg 160034 ∧ rd c' bMerge 7 = c.nreg 160084 ∧
      rd c' bMerge 9 = c.nreg 160000 ∧
      (∀ r, (r < 100000 ∨ 100009 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold setupB
  simp only [rd_merge, Nat.reduceAdd]
  exec_block
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem postB_exec {c : Config} (hw : WordsBounded W c) {E TD f prev ptr i j : ℕ}
    (hA : c.nreg ALLOC = E) (h37 : c.nreg 160037 = TD) (h8 : c.nreg 100008 = f)
    (h63 : c.nreg 160063 = prev) (h65 : c.nreg 160065 = ptr) (h62 : c.nreg 160062 = i)
    (h64 : c.nreg 160064 = j)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h83 : c.nreg 160083 = 3)
    (h84 : c.nreg 160084 = 4) (hW : E + 3 ≤ W) (hWp : ptr + 4 ≤ W) (hWi : i + 2 ≤ W)
    (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W postB c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nmem E = TD ∧ c'.nmem (E + 1) = f ∧ c'.nmem (E + 2) = prev ∧
      (∀ a, (a < E ∨ E + 3 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg ALLOC = E + 3 ∧ c'.nreg 160063 = E ∧ c'.nreg 160065 = ptr + 4 ∧
      c'.nreg 160062 = i + 2 ∧ c'.nreg 160064 = j + 1 ∧
      (∀ r, r ≠ 160092 → r ≠ 160093 → r ≠ 160063 → r ≠ 160065 → r ≠ 160062 → r ≠ 160064 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold postB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h65, h62, h64, h24, h80, h83, h84]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h37, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h8, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h63, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · config_simp; simp only [hA, h83]
  · config_simp; simp only [hA]
  · config_simp; simp only [h65, h84]
  · config_simp; simp only [h62, h80]
  · config_simp; simp only [h64, h24]
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

end proofs

end

end Chazelle.Core.L41
