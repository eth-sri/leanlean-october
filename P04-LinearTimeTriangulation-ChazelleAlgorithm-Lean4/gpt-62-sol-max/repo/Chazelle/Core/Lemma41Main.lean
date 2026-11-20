module

public import Chazelle.Core.Lemma41Leaf
public import Chazelle.Core.GradeCtx

/-!
# WP-J, part 25: Lemma 4.1 on the RAM

`l41S sM`: the prologue (constants, table reads, `Gλ`, the whole host), the greedy cover of
`[a, a + L]` into grade chains (`coverS`), their level array (`l0S`), the merge tree (`treeS`),
and the output (the NF of the single node).  `l41_exec`: the contract of `Lemma41Spec` for one
merge program `sM` meeting `MergeMeets` with monotone `F, G, H`, with the explicit step bound
`l41Big` (the cost bridge to `lemma41Nat` is separate).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle Chazelle.Merge

@[expose] public section

/-- `decide` for literal goals (fast, no context scan), `omega` otherwise. -/
macro "l41dec" : tactic => `(tactic| first | decide | omega)

/-- `160066 := 160015` (the base of the leaves' level array). -/
def baseB : Stmt := block [.copyN 160066 160015]

/-- The output: the NF of the single node. -/
def epiB : Stmt := block [.addN 160031 160066 160024, .loadN 160004 160031]

/-- The prologue: constants, table reads, `Gλ`, the host. -/
def l41A : Stmt := .seq proC (.seq proL (.seq clogS (.seq mulS proH)))

/-- The leaves: the cover, the base of the level array, the level array. -/
def l41B : Stmt := .seq coverS (.seq baseB l0S)

/-- **Lemma 4.1 on the RAM.** -/
def l41S (sM : Stmt) : Stmt := .seq l41A (.seq l41B (.seq (treeS sM) epiB))

/-- The chord bound of the leaves. -/
noncomputable def leafKb (lam a L : ℕ) : ℕ :=
  (((leafShp lam (a + L) a).filter (leafP (gradeGran (lam - 1)))).map kb).sum

/-- **The step bound of Lemma 4.1** (before the cost bridge). -/
noncomputable def l41Big (κ F G H : ℕ → ℕ) (lam a L : ℕ) : ℕ :=
  40 * lam ^ 2 + 169 * lam + 84 + 11 * (cover lam (a + L) a).length +
    Nat.clog 2 (cover lam (a + L) a).length *
      (lvBound κ F G H (gradeGran lam) (gradeGran (lam - 1)) (cover lam (a + L) a).length L
        (leafKb lam a L) + 2)

theorem bandOf_not_l41 {r : ℕ} (h : bandOf r ∉ l41Bands) :
    (r < 160000 ∨ 170000 ≤ r) ∧ bandOf r ∉ mergeBands ∪ oracleBands := by
  unfold l41Bands at h
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at h
  refine ⟨?_, by simp only [Finset.mem_union, not_or]; exact h.1⟩
  have := h.2
  unfold bandOf bL41 at this
  omega

theorem okModel_chain {P : Polygon} (hG : GoodEnv P) (C : Chain) (hC : C.P = Qof P) :
    OkModel P (chainModel C) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : 1 ≤ P.n := by have := hG.1.1; omega
  refine ⟨Host.whole P.n, C, by simp [HostOk, Host.whole], by rw [hQn]; exact hostRegular_whole hn,
    ?_, ?_, rfl⟩
  · rw [hC]; have := poly_whole (Qof P) (by omega); rw [hQn] at this; exact this.symm
  · rw [hC]; exact (shearInvariance (epsOf P) P).1 hG.1

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem baseB_exec {c : Config} (hw : WordsBounded W c) :
    ∃ c' k, Exec P W baseB c c' k ∧ k = 1 ∧ WordsBounded W c' ∧
      c'.nreg 160066 = c.nreg 160015 ∧ (∀ r, r ≠ 160066 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold baseB
  exec_block
  refine ⟨rfl, ‹_›, by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 4000000 in
theorem epiB_exec {c : Config} (hw : WordsBounded W c) {B : ℕ} (h66 : c.nreg 160066 = B)
    (h24 : c.nreg 160024 = 1) (hW : B + 1 ≤ W) :
    ∃ c' k, Exec P W epiB c c' k ∧ k = 2 ∧ WordsBounded W c' ∧
      c'.nreg 160004 = c.nmem (B + 1) ∧
      (∀ r, r ≠ 160004 → r ≠ 160031 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold epiB
  exec_block
  all_goals try (config_simp; (try simp only [h66, h24]); omega)
  refine ⟨rfl, ‹_›, by config_simp; simp only [h66, h24], fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

end proofs

end

end Chazelle.Core.L41
