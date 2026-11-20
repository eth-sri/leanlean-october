module

public import Chazelle.Machine.FrameFields

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.OraclePrepPairSort

/-!
# Lemma 3.6 (WP-H), preprocessing part 16: sorting and deduplicating the raw pairs

`dS`: the handles are saved in band `bDecomp` (`60001 …`), an item array `0 … nZ - 1` is built,
sorted by the lexicographic order of the raw pairs (`SortR.sortStmt lexCmp`), and the pairs are
appended, without repetitions, to the chord arrays after the star chords (`dS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- The dedup body: the pair at sorted position `t`, kept iff first or new. -/
def dBody : Stmt :=
  .seq (block [.addN 60015 60007 60010, .loadN 60015 60015, .addN 60016 60004 60015,
      .loadN 60012 60016, .addN 60016 60005 60015, .loadN 60013 60016])
    (.ifLtN 120012 60010
      (.seq (block [.subN 60015 60010 120011, .addN 60015 60007 60015, .loadN 60015 60015,
          .addN 60016 60004 60015, .loadN 60018 60016, .addN 60016 60005 60015,
          .loadN 60019 60016])
        (ifEq 60012 60018 (ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1)))
          (.instr (.constN 60011 1))))
      (.instr (.constN 60011 1)))

/-- The registers written by `dBody`. -/
def BDB (r : ℕ) : Bool := decide (60011 ≤ r ∧ r ≤ 60019 ∧ r ≠ 60014 ∧ r ≠ 60017)

/-- The memory read by the dedup body. -/
structure DMem (m : ℕ → ℕ) (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) : Prop where
  s_eq : ∀ t, t < n → m (Sb + t) = s t
  s_lt : ∀ t, t < n → s t < n
  p1 : ∀ i, i < n → m (Z1 + i) = P1 i
  p2 : ∀ i, i < n → m (Z2 + i) = P2 i

section

variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)

include P hw in
theorem dBody_exec {Sb Z1 Z2 n t : ℕ}
    {s P1 P2 : ℕ → ℕ} (hM : DMem c.nmem Sb Z1 Z2 n s P1 P2) (h7 : c.nreg 60007 = Sb)
    (h4 : c.nreg 60004 = Z1) (h5 : c.nreg 60005 = Z2) (h1 : c.nreg 120011 = 1)
    (h0 : c.nreg 120012 = 0) (ht : c.nreg 60010 = t) (htn : t < n) (hSW : Sb + n ≤ W)
    (hZW : Z1 + n ≤ W) (hZW' : Z2 + n ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W dBody c c' k ∧ k ≤ 30 ∧ FrameB BDB c c' ∧
      (dedupF n (fun i => (P1 i, P2 i)) s t = none → c'.nreg 60011 = 0) ∧
      ∀ x, dedupF n (fun i => (P1 i, P2 i)) s t = some x →
        c'.nreg 60011 = 1 ∧ c'.nreg 60012 = x.1 ∧ c'.nreg 60013 = x.2 := by
  have hwr : wr BDB dBody = true := by decide
  have hs := hM.s_lt t htn
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 60015 60007 60010,
      .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60012 60016, .addN 60016 60005 60015,
      .loadN 60013 60016]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 60015 (s t)) 60016 (Z2 + s t)) 60012 (P1 (s t))) 60013
        (P2 (s t)) := by
    exec_block
    · rw [h7, ht]; omega
    · ram_post
    · ram_post
    · refine ⟨rfl, ?_⟩
      config_simp; rw [h7, ht, h4, h5, hM.s_eq t htn, hM.p1 _ hs, hM.p2 _ hs]
      funext r; simp only [upd]; split_ifs <;> first | omega
  have w₁ := e₁.wb_right
  have R₁ : ∀ r, r ≠ 60015 → r ≠ 60016 → r ≠ 60012 → r ≠ 60013 → c₁.nreg r = c.nreg r :=
    fun r a b c' d => by simp_all
  have x12 : c₁.nreg 60012 = P1 (s t) := by rw [n₁]; config_simp
  have x13 : c₁.nreg 60013 = P2 (s t) := by rw [n₁]; config_simp
  suffices H : ∃ c₂ k₂, Exec P W (.ifLtN 120012 60010
      (.seq (block [.subN 60015 60010 120011, .addN 60015 60007 60015, .loadN 60015 60015,
          .addN 60016 60004 60015, .loadN 60018 60016, .addN 60016 60005 60015,
          .loadN 60019 60016])
        (ifEq 60012 60018 (ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1)))
          (.instr (.constN 60011 1))))
      (.instr (.constN 60011 1))) c₁ c₂ k₂ ∧ k₂ ≤ 24 ∧
      c₂.nreg 60012 = P1 (s t) ∧ c₂.nreg 60013 = P2 (s t) ∧
      c₂.nreg 60011 = (if t = 0 ∨ (P1 (s t), P2 (s t)) ≠ (P1 (s (t - 1)), P2 (s (t - 1)))
        then 1 else 0) by
    obtain ⟨c₂, k₂, e₂, hk₂, a, b, f⟩ := H
    have ex : Exec P W dBody c c₂ _ := .seq e₁ e₂
    refine ⟨c₂, _, ex, by omega, exec_frameB ex hwr, fun hn => ?_, fun x hx => ?_⟩
    · unfold dedupF at hn
      split_ifs at hn with hc
      rw [f, ite_eq_right (fun h' => hc ⟨htn, h'⟩)]
    · unfold dedupF at hx
      split_ifs at hx with hc
      cases hx
      exact ⟨by rw [f, ite_eq_left hc.2], a, b⟩
  by_cases hz : t = 0
  · have ht' : ¬ c₁.nreg 120012 < c₁.nreg 60010 := by
      simp_all
    exact ⟨_, _, .ifLtN_false ht' (Exec.constN w₁ 60011 1 hW), by omega, by config_simp; exact x12,
      by config_simp; exact x13, by simp_all⟩
  · have ht' : c₁.nreg 120012 < c₁.nreg 60010 := by
      ram_simp [R₁, h0, ht] <;> omega
    have hs' := hM.s_lt (t - 1) (by omega)
    obtain ⟨c₂, k₂, e₂, hk₂, n₂⟩ : ∃ c₂ k₂, Exec P W (block [.subN 60015 60010 120011,
        .addN 60015 60007 60015, .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60018 60016,
        .addN 60016 60005 60015, .loadN 60019 60016]) c₁ c₂ k₂ ∧ k₂ = 7 ∧
        c₂.nreg = upd (upd (upd (upd c₁.nreg 60015 (s (t - 1))) 60016 (Z2 + s (t - 1))) 60018
          (P1 (s (t - 1)))) 60019 (P2 (s (t - 1))) := by
      have a7 : c₁.nreg 60007 = Sb := by simp_all
      have a4 : c₁.nreg 60004 = Z1 := by simp_all
      have a5 : c₁.nreg 60005 = Z2 := by simp_all
      have a10 : c₁.nreg 60010 = t := by
        simp_all
      have a11 : c₁.nreg 120011 = 1 := by
        simp_all
      have hmem : c₁.nmem = c.nmem :=
        (exec_frameB e₁ (B := BDB) (by decide)).2.2.1
      exec_block
      · config_simp; rw [a7, a10, a11]; omega
      · ram_simp [a7, a10, a11, a4, hmem, hM.s_eq] <;> omega
      · ram_simp [a7, a10, a11, a5, hmem, hM.s_eq] <;> omega
      · refine ⟨rfl, ?_⟩
        config_simp; ram_rw [a7, a10, a11, a4, a5, hmem, hM.s_eq, hM.p1 _ hs', hM.p2 _ hs']
        funext r; simp only [upd]; split_ifs <;> first | omega
    have w₂ := e₂.wb_right
    have y12 : c₂.nreg 60012 = P1 (s t) := by simp_all
    have y13 : c₂.nreg 60013 = P2 (s t) := by simp_all
    have y18 : c₂.nreg 60018 = P1 (s (t - 1)) := by rw [n₂]; config_simp
    have y19 : c₂.nreg 60019 = P2 (s (t - 1)) := by rw [n₂]; config_simp
    by_cases e1 : P1 (s t) = P1 (s (t - 1))
    · have q1 : c₂.nreg 60012 = c₂.nreg 60018 := by rw [y12, y18, e1]
      by_cases e2 : P2 (s t) = P2 (s (t - 1))
      · have q2 : c₂.nreg 60013 = c₂.nreg 60019 := by rw [y13, y19, e2]
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 (ifEq_eq_exec q2
          (Exec.constN w₂ 60011 0 (Nat.zero_le _))))), by omega, by config_simp; exact y12,
          by config_simp; exact y13, by
            ram_post⟩
      · have q2 : c₂.nreg 60013 ≠ c₂.nreg 60019 := by rwa [y13, y19]
        obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) (S := .instr (.constN 60011 0)) q2
          (Exec.constN w₂ 60011 1 hW)
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 e')), by omega,
          by config_simp; exact y12, by config_simp; exact y13, by
            config_simp; rw [ite_eq_left (Or.inr (fun h' => e2 (Prod.mk.inj h').2))]⟩
    · have q1 : c₂.nreg 60012 ≠ c₂.nreg 60018 := by rwa [y12, y18]
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W)
        (S := ifEq 60013 60019 (.instr (.constN 60011 0)) (.instr (.constN 60011 1))) q1
        (Exec.constN w₂ 60011 1 hW)
      exact ⟨_, _, .ifLtN_true ht' (.seq e₂ e'), by omega, by config_simp; exact y12,
        by config_simp; exact y13, by
          config_simp; rw [ite_eq_left (Or.inr (fun h' => e1 (Prod.mk.inj h').1))]⟩

/-! ## Saving the handles, the items, the sort -/

/-- Save the handles into band `bDecomp`. -/
def dSave : Stmt :=
  block [.copyN 60001 110072, .copyN 60002 110073, .copyN 60003 110074, .copyN 60004 110293,
    .copyN 60005 110294, .copyN 60006 110295]

/-- **Save, build the items, sort them by their raw pairs.** -/
def dSort : Stmt :=
  .seq dSave sortCore

include P hw in
theorem dSort_exec
    {CH1 CH2 nI Z1 Z2 n A₀ : ℕ} (h72 : c.nreg 110072 = CH1) (h73 : c.nreg 110073 = CH2)
    (h74 : c.nreg 110074 = nI) (h93 : c.nreg 110293 = Z1) (h94 : c.nreg 110294 = Z2)
    (h95 : c.nreg 110295 = n) (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₀)
    (hZ1 : Z1 + n ≤ A₀) (hZ2 : Z2 + n ≤ A₀)
    (hroom : A₀ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W dSort c c' k ∧ k ≤ 7 * n + SortR.sortCost 20 n + 20 ∧
      FrameN dBands c c' ∧ A₀ + n ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + n + SortR.sortCost 20 n ∧
      c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧ c'.nreg 60003 = nI ∧ c'.nreg 60004 = Z1 ∧
      c'.nreg 60005 = Z2 ∧ c'.nreg 60006 = n ∧
      A₀ + n ≤ c'.nreg 60007 ∧ c'.nreg 60007 + n ≤ c'.nreg 9999 ∧
      SortedSeq (fun i => (c.nmem (Z1 + i), c.nmem (Z2 + i))) (fun t => c'.nmem (c'.nreg 60007 + t)) n ∧
      (∀ i, i < n → ∃ t, t < n ∧ c'.nmem (c'.nreg 60007 + t) = i) ∧
      (∀ t, t < n → c'.nmem (c'.nreg 60007 + t) < n) := by
  -- 1. save
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W dSave c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 60001 CH1) 60002 CH2) 60003 nI) 60004 Z1)
        60005 Z2) 60006 n ∧ Machine.NatRegFrame c c₁ := by
    ram_exec
  have hframe := exec_frameB e₁ (B := fun r => decide (60001 ≤ r ∧ r ≤ 60006)) (by decide)
  have F₁ : FrameN dBands c c₁ := Frame.toN (NFLoc.frame_of_frameB (S := dBands) hframe (fun r hr => by
    simp only [decide_eq_true_eq] at hr
    have he : bandOf r = bDecomp := by reg_omega
    exact ⟨by rw [he]; decide, by reg_omega⟩) k₁)
  have a := hframe.1 9999 (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, hA₂, hb₂, hkeep, hs, hn, hsort, hsurj, hrange⟩ :=
    sortCore_exec (P := P) e₁.wb_right (c := c₁) (Z1 := Z1) (Z2 := Z2) (n := n)
      (by rw [n₁]; config_simp) (by rw [n₁]; config_simp) (by rw [n₁]; config_simp)
      ((hframe.1 _ (by decide)).trans h1) (a.trans hAl) hZ1 hZ2 hroom
  have H (r : ℕ) (hr : 60001 ≤ r ∧ r ≤ 60006) : c₂.nreg r = c₁.nreg r :=
    hkeep r (by reg_omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, F₁.trans F₂ (by exact a.ge), hA₂, hb₂,
    ?_, ?_, ?_, ?_, ?_, ?_, hs, hn, (by simpa only [m₁] using hsort), hsurj, hrange⟩ <;>
    ram_rw [H, n₁] <;> config_simp

/-- **The dedup emission** into the chord arrays. -/
def dEmit : Stmt := emitS 60010 60006 120011 60011 60012 60013 60001 60002 60003 60014 dBody

/-- The environment of the dedup emission. -/
def DEnv (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 60004 = Z1 ∧ d.nreg 60005 = Z2 ∧ d.nreg 60007 = Sb ∧ d.nreg 120011 = 1 ∧
    d.nreg 120012 = 0 ∧ DMem d.nmem Sb Z1 Z2 n s P1 P2

include P hw in
theorem dEmit_exec
    {CH1 CH2 nI Sb Z1 Z2 n : ℕ} {s P1 P2 : ℕ → ℕ} (hE : DEnv Sb Z1 Z2 n s P1 P2 c)
    (h1 : c.nreg 60001 = CH1) (h2 : c.nreg 60002 = CH2) (h3 : c.nreg 60003 = nI)
    (h6 : c.nreg 60006 = n) (hC : CH1 + nI + n ≤ CH2) (hZ : CH2 + nI + n ≤ Z1)
    (hZ12 : Z1 ≤ Z2) (hZS : Z2 ≤ Sb) (hSW : Sb + n ≤ W) :
    ∃ c' k, Exec P W dEmit c c' k ∧ k ≤ n * 40 + 3 ∧
      (∀ r, BDB r = false → r ≠ 60010 → r ≠ 60003 → r ≠ 60014 → c'.nreg r = c.nreg r) ∧
      (∀ r, BDB r = false → c'.rreg r = c.rreg r) ∧
      c'.nreg 60003 = nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ∧
      PairsAt c'.nmem (CH1 + nI) (CH2 + nI) (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n) ∧
      (∀ a, (a < CH1 + nI ∨ (CH1 + nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ≤ a ∧
        a < CH2 + nI) ∨ CH2 + nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      Machine.RealMemOutputEq c c' := by
  obtain ⟨c', k, ex, hk, r', rr', cnt, pr, mm, rm, o, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 60010) (rn := 60006) (r1 := 120011) (rf := 60011) (rv1 := 60012) (rv2 := 60013)
    (rR1 := 60001) (rR2 := 60002) (rc := 60003) (rt := 60014) (body := dBody) (B := BDB)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (R1 := CH1) (R2 := CH2) (c₀ := nI) (n := n) (κ := 30) (DEnv Sb Z1 Z2 n s P1 P2)
    (fun d d' hJ hr hm => by
      obtain ⟨a4, a5, a7, a11, a12, hM⟩ := hJ
      refine ⟨by ram_simp [hr, a4],
        by ram_simp [hr, a5],
        by ram_simp [hr, a7],
        by ram_simp [hr, a11],
        by ram_simp [hr, a12], ⟨fun t ht => ?_,
        hM.s_lt, fun i hi => ?_, fun i hi => ?_⟩⟩
      · rw [hm _ ((by omega))]; exact hM.s_eq t ht
      · rw [hm _ ((by omega))]; exact hM.p1 i hi
      · rw [hm _ ((by omega))]; exact hM.p2 i hi)
    (dedupF n (fun i => (P1 i, P2 i)) s)
    (fun i d hi hJ hwd hri => by
      obtain ⟨a4, a5, a7, a11, a12, hM⟩ := hJ
      exact (ram_app% (dBody_exec hwd hM a7 a4 a5 a11 a12 hri hi hSW ?_ ?_ ?_)))
    hw hE h6 hE.2.2.2.1 h1 h2 h3 hC (by omega)
  exact ⟨c', k, ex, by nlinarith, r', rr', cnt, pr, mm, rm, o⟩

end

end

end OracleR

end Chazelle.Core
