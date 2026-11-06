module

public import Chazelle.Core.FuseAsmSort

/-!
# WP-F fusion assembly, part 6: removing duplicate triples

The collected triples may repeat.  They are sorted (`SortR.sortStmt cmp3` on the indices
`0 … K - 1`, written by `ixLoop`), and the scan `dsLoop` keeps an entry iff it is the first one or
differs from its predecessor (`dd`).  For a sorted list this removes all repetitions
(`dd_nodup`) and keeps every element (`mem_dd`).

Registers (band `bFuse`): `70200` index, `70201` bound `K`, `70105` the constant `1`,
`70220 …` the scan.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The list function -/

variable {α : Type*} [DecidableEq α]

/-- The entries kept by the scan: the first one and those differing from their predecessor. -/
def keep (l : List α) (d : α) (j : ℕ) : Bool := j = 0 ∨ l.getD j d ≠ l.getD (j - 1) d

/-- The scan applied to the first `n` entries. -/
def ddp (l : List α) (d : α) (n : ℕ) : List α :=
  ((List.range n).filter (keep l d)).map fun j => l.getD j d

/-- The scan. -/
def dd (l : List α) (d : α) : List α := ddp l d l.length

theorem ddp_succ (l : List α) (d : α) (n : ℕ) :
    ddp l d (n + 1) = ddp l d n ++ (if keep l d n then [l.getD n d] else []) := by
  unfold ddp
  rw [List.range_succ, List.filter_append, List.map_append]
  by_cases h : keep l d n <;> simp [h]

theorem mem_dd (l : List α) (d : α) (x : α) : x ∈ dd l d ↔ x ∈ l := by
  unfold dd ddp
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, -⟩, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    -- the first occurrence
    classical
    let P : ℕ → Prop := fun i => i < l.length ∧ l.getD i d = l[j]
    have hP : ∃ i, P i := ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl⟩
    let i := Nat.find hP
    have hi : P i := Nat.find_spec hP
    refine ⟨i, ⟨hi.1, ?_⟩, hi.2⟩
    unfold keep
    by_cases h0 : i = 0
    · simp [h0]
    · have hmin := Nat.find_min hP (show i - 1 < i by omega)
      simp only [decide_eq_true_eq, Bool.decide_or, Bool.or_eq_true]
      right
      intro heq
      apply hmin
      refine ⟨by have := hi.1; omega, ?_⟩
      rw [← heq]; exact hi.2

/-- **The scan of a sorted list has no repetitions.** -/
theorem dd_nodup {r : α → α → Prop} (hanti : ∀ x y, r x y → r y x → x = y) {l : List α}
    (hs : l.Pairwise r) (d : α) : (dd l d).Nodup := by
  unfold dd ddp
  refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro i hi j hj hij
  simp only [List.mem_filter, List.mem_range] at hi hj
  by_contra hne
  -- wlog `i < j`
  have key : ∀ a b, a < b → b < l.length → keep l d b = true → l.getD a d = l.getD b d → False := by
    intro a b hab hb hk heq
    have hb0 : b ≠ 0 := by omega
    unfold keep at hk
    simp only [hb0, false_or, decide_eq_true_eq, decide_eq_true_eq] at hk
    apply hk
    -- `l[a] = l[b]` and `a ≤ b - 1 < b`: sorted, so `l[b - 1] = l[b]`
    have ga : l.getD a d = l[a] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have gb : l.getD b d = l[b] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]; rfl
    have gc : l.getD (b - 1) d = l[b - 1] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [gb, gc]
    rw [ga, gb] at heq
    rcases Nat.lt_or_ge a (b - 1) with h | h
    · have h1 : r l[a] l[b - 1] := List.pairwise_iff_getElem.1 hs _ _ (by omega) (by omega) h
      have h2 : r l[b - 1] l[b] := List.pairwise_iff_getElem.1 hs _ _ (by omega) hb (by omega)
      rw [heq] at h1
      exact (hanti _ _ h2 h1).symm
    · have : a = b - 1 := by omega
      subst this; exact heq.symm
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key i j h hj.1 hj.2 hij
  · exact key j i h hi.1 hi.2 hij.symm

/-! ## The index loop -/

/-- Write the index and advance. -/
def ixBody : Stmt := block [.storeN ALLOC 70200, .addN ALLOC ALLOC 70105, .addN 70200 70200 70105]

/-- Write the indices `0 … K - 1` at the allocator. -/
def ixLoop : Stmt := .whileLtN 70200 70201 ixBody

/-- The invariant of the index loop. -/
structure IXI (W K S : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  alloc : c.nreg ALLOC = S + c.nreg 70200
  regs : ∀ r, r ≠ 70200 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : ∀ a, a < S → c.nmem a = c₀.nmem a
  done : ∀ j, j < c.nreg 70200 → c.nmem (S + j) = j
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 2000000 in
theorem ixLoop_exec {P : Polygon} {W K S : ℕ} {c₀ : Config} (h05 : c₀.nreg 70105 = 1)
    (h01 : c₀.nreg 70201 = K) (hW : S + K + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), IXI W K S c₀ c → c.nreg 70200 + n = K →
      ∃ c' k, Exec P W ixLoop c c' k ∧ k ≤ 5 * n + 2 ∧ n ≤ k ∧ IXI W K S c₀ c' ∧ c'.nreg 70200 = K
  | 0, c, hI, hn => by
    have h01' : c.nreg 70201 = K := by rw [hI.regs 70201 (by decide) (by decide), h01]
    exact ⟨c, 2, .whileLtN_false (by rw [h01']; omega) hI.wb, by omega, by omega, hI, by omega⟩
  | n + 1, c, hI, hn => by
    have h01' : c.nreg 70201 = K := by rw [hI.regs 70201 (by decide) (by decide), h01]
    have h05' : c.nreg 70105 = 1 := by rw [hI.regs 70105 (by decide) (by decide), h05]
    obtain ⟨i, hi⟩ : ∃ i, c.nreg 70200 = i := ⟨_, rfl⟩
    have hA : c.nreg 9999 = S + i := by rw [← hi]; exact hI.alloc
    have hw := hI.wb
    obtain ⟨c', k, e, hk, q⟩ : ∃ c' k, Exec P W ixBody c c' k ∧ k = 3 ∧
        (c'.nreg 70200 = i + 1 ∧ c'.nreg ALLOC = S + (i + 1) ∧
        (∀ r, r ≠ 70200 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c'.nmem = upd c.nmem (S + i) i ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
      unfold ixBody
      exec_block
      all_goals try (simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hA, hi, h05', ALLOC]; omega)
      refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, ?_, rfl, rfl, rfl⟩
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hi,
          h05', ALLOC]
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA,
          h05', ALLOC]; ring
      · have a2' : r ≠ 9999 := a2
        simp (disch := omega) only [Machine.upd_other]
      · simp (disch := omega) only [hA, hi, ALLOC]
    obtain ⟨q0, qA, qr, qm, qrr, qrm, qo⟩ := q
    have hI' : IXI W K S c₀ c' := by
      refine ⟨e.wb_right, by rw [qA, q0], fun r a1 a2 => by rw [qr r a1 a2,
        hI.regs r a1 a2], fun a ha => by rw [qm, upd_other _ _ _ (by omega), hI.low a ha],
        fun j hj => ?_, by rw [qrr, hI.rr], by rw [qrm, hI.rm], by rw [qo, hI.out]⟩
      rw [q0] at hj
      rw [qm]
      rcases Nat.lt_or_ge j i with h | h
      · rw [upd_other _ _ _ (by omega)]; exact hI.done j (by omega)
      · have : j = i := by omega
        subst this; rw [upd_same]
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := ixLoop_exec h05 h01 hW n c' hI' (by omega)
    exact ⟨c'', k + 2 + k₂, .whileLtN_true (by rw [hi, h01']; omega) e e₂, by omega, by omega, hI'', hK⟩

theorem seg_range {m : ℕ → ℕ} {S K : ℕ} (h : ∀ j, j < K → m (S + j) = j) :
    SortL.seg m S K = List.range K := by
  apply List.ext_getElem (by simp [SortL.seg])
  intro j h1 h2
  simp only [SortL.seg, List.getElem_map, List.getElem_range]
  exact h j (by simpa using h2)

end

end FuseAsm

end Chazelle.Core
