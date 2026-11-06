module

public import Chazelle.Core.FuseAsmColl
public import Chazelle.Core.FuseAsmHt

/-!
# WP-F fusion assembly, part 12: collecting the answers with the heights of their queries

`clqLoop` scans a query list (three words per query) and its result list (four words per
result) in parallel and appends, for every result with flag `1`, the triple
`(code - 1, lp, rp)` at the allocator (`collectQ`), counting the triples in `70110`.  Registers
(band `bFuse`):

| register | content |
|---|---|
| `70110` | number of triples written so far |
| `70111` | number of results |
| `70112` | loop index |
| `70113` | cursor in the result list |
| `70115` | cursor in the query list |
| `70114`, `70119` | scratch |
| `70105`, `70108`, `70116`, `70117`, `70118` | constants `1`, `0`, `3`, `4`, `2` |
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Copy the triple of the current result, with the height index of the current query. -/
def clqCopy : Stmt := block [.addN 70119 70115 70105, .loadN 70114 70119,
  .subN 70114 70114 70105, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70119 70113 70118, .loadN 70114 70119, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70119 70119 70105, .loadN 70114 70119, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70110 70110 70105]

/-- One result. -/
def clqBody : Stmt :=
  .seq (block [.loadN 70114 70113])
    (.seq (.ifLtN 70108 70114 (.ifLtN 70114 70118 clqCopy .skip) .skip)
      (block [.addN 70113 70113 70117, .addN 70115 70115 70116, .addN 70112 70112 70105]))

/-- The collection loop. -/
def clqLoop : Stmt := .whileLtN 70112 70111 clqBody

set_option maxHeartbeats 4000000 in
theorem clqCopy_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {s t a K : ℕ}
    (h13 : c.nreg 70113 = s) (h15 : c.nreg 70115 = t) (hA : c.nreg ALLOC = a)
    (h05 : c.nreg 70105 = 1) (h18 : c.nreg 70118 = 2) (h10 : c.nreg 70110 = K)
    (hs : s + 3 ≤ W) (ht : t + 1 ≤ W) (ha : a + 3 ≤ W) (hK : K + 1 ≤ W) (hsa : s + 3 < a)
    (_hta : t + 1 < a) :
    ∃ c' k, Exec P W clqCopy c c' k ∧ k = 14 ∧ c'.nreg ALLOC = a + 3 ∧
      (∀ x, (x < a ∨ a + 3 ≤ x) → c'.nmem x = c.nmem x) ∧
      c'.nmem a = c.nmem (t + 1) - 1 ∧ c'.nmem (a + 1) = c.nmem (s + 2) ∧
      c'.nmem (a + 2) = c.nmem (s + 3) ∧ c'.nreg 70110 = K + 1 ∧
      (∀ r, r ≠ 70110 → r ≠ 70114 → r ≠ 70119 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clqCopy
  have hA' : c.nreg 9999 = a := hA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h13, h15, hA', h05, h18, h10, ALLOC]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h13, h15, hA', h05, h18, h10, ALLOC])
  · have a4' : r ≠ 9999 := a4
    simp (disch := omega) only [Machine.upd_other]

/-- The invariant of the collection loop (`pre`: the triples written before the loop). -/
structure CLQI (W : ℕ) (L : List (ℕ × ℕ × ℕ)) (R : List (ℕ × ℕ × ℕ × ℕ)) (QB RB LB : ℕ)
    (pre : List (ℕ × ℕ × ℕ)) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  cur : c.nreg 70113 = RB + 4 * c.nreg 70112
  qcur : c.nreg 70115 = QB + 3 * c.nreg 70112
  alloc : c.nreg ALLOC = LB + 3 * (pre ++ collectQ (L.take (c.nreg 70112))
    (R.take (c.nreg 70112))).length
  cnt : c.nreg 70110 = (pre ++ collectQ (L.take (c.nreg 70112)) (R.take (c.nreg 70112))).length
  regs : ∀ r, r ≠ 70110 → r ≠ 70112 → r ≠ 70113 → r ≠ 70114 → r ≠ 70115 → r ≠ 70119 →
    r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : ∀ a, a < LB + 3 * pre.length → c.nmem a = c₀.nmem a
  list : ChordListAt c.nmem LB (pre ++ collectQ (L.take (c.nreg 70112)) (R.take (c.nreg 70112)))
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 8000000 in
theorem clqBody_step {P : Polygon} {W : ℕ} {L : List (ℕ × ℕ × ℕ)} {R : List (ℕ × ℕ × ℕ × ℕ)}
    {QB RB LB : ℕ} {pre : List (ℕ × ℕ × ℕ)} {c₀ c : Config}
    (hI : CLQI W L R QB RB LB pre c₀ c) (ht : c.nreg 70112 < R.length) (h05 : c₀.nreg 70105 = 1)
    (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70116 = 3) (h17 : c₀.nreg 70117 = 4)
    (h18 : c₀.nreg 70118 = 2) (hLR : L.length = R.length)
    (hR : ResultListAt c₀.nmem RB R) (hQ : ChordListAt c₀.nmem QB L)
    (hRB : RB + 4 * R.length ≤ LB) (hQB : QB + 3 * L.length ≤ LB)
    (hW : LB + 3 * pre.length + 3 * R.length + 4 ≤ W) (hWK : pre.length + R.length + 1 ≤ W) :
    ∃ c' k, Exec P W clqBody c c' k ∧ CLQI W L R QB RB LB pre c₀ c' ∧ k ≤ 22 ∧ 4 ≤ k ∧
      c'.nreg 70112 = c.nreg 70112 + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, c.nreg 70112 = j := ⟨_, rfl⟩
  rw [hj] at ht
  have hjL : j < L.length := by omega
  have hreg : ∀ r, r ≠ 70110 → r ≠ 70112 → r ≠ 70113 → r ≠ 70114 → r ≠ 70115 → r ≠ 70119 →
      r ≠ ALLOC → c.nreg r = c₀.nreg r := hI.regs
  have r05 : c.nreg 70105 = 1 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h05]
  have r08 : c.nreg 70108 = 0 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h08]
  have r16 : c.nreg 70116 = 3 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h16]
  have r17 : c.nreg 70117 = 4 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h17]
  have r18 : c.nreg 70118 = 2 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h18]
  have hcur : c.nreg 70113 = RB + 4 * j := by rw [hI.cur, hj]
  have hqcur : c.nreg 70115 = QB + 3 * j := by rw [hI.qcur, hj]
  obtain ⟨q0, q1, q2, q3⟩ := hR j ht
  obtain ⟨p0, p1, p2⟩ := hQ j hjL
  set r := R.getD j (0, 0, 0, 0) with hr
  set q := L.getD j (0, 0, 0) with hq
  set C0 := pre ++ collectQ (L.take j) (R.take j) with hC0
  have hmem : ∀ k, k < 4 → c.nmem (RB + 4 * j + k) = c₀.nmem (RB + 4 * j + k) :=
    fun k hk => hI.low _ (by omega)
  have hqmem : c.nmem (QB + 3 * j + 1) = c₀.nmem (QB + 3 * j + 1) := hI.low _ (by omega)
  have hlenj : (collectQ (L.take j) (R.take j)).length ≤ j :=
    (collectQ_length_le _ _).trans (by rw [List.length_take]; omega)
  have htake : R.take (j + 1) = R.take j ++ [r] := by
    rw [hr, getD_lt ht]; exact List.take_succ_eq_append_getElem ht
  have htakeL : L.take (j + 1) = L.take j ++ [q] := by
    rw [hq, getD_lt hjL]; exact List.take_succ_eq_append_getElem hjL
  have hlt : (L.take j).length = (R.take j).length := by simp [List.length_take, hLR]
  have hlenC : C0.length ≤ pre.length + j := by rw [hC0, List.length_append]; omega
  -- the flag
  have e₁ := Exec.loadN (P := P) hI.wb 70114 70113
  set c₁ : Config := { c with nreg := upd c.nreg 70114 (c.nmem (c.nreg 70113)) } with hc₁
  have v14 : c₁.nreg 70114 = r.1 := by
    rw [hc₁]; simp only [upd_same]; rw [hcur]
    have := hmem 0 (by omega); simp only [add_zero] at this; rwa [this]
  have q₁ : ∀ x, x ≠ 70114 → c₁.nreg x = c.nreg x := fun x hx => by
    rw [hc₁]; simp [upd_other _ _ _ hx]
  have hw₁ : WordsBounded W c₁ := e₁.wb_right
  -- the copy (or not)
  obtain ⟨c₂, k₂, e₂, hk₂, a₂, n₂, m₂, l₂, q₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 70108 70114 (.ifLtN 70114 70118 clqCopy .skip) .skip) c₁ c₂ k₂ ∧ k₂ ≤ 16 ∧
      c₂.nreg ALLOC = LB + 3 * (pre ++ collectQ (L.take (j + 1)) (R.take (j + 1))).length ∧
      c₂.nreg 70110 = (pre ++ collectQ (L.take (j + 1)) (R.take (j + 1))).length ∧
      (∀ a, a < LB + 3 * C0.length → c₂.nmem a = c.nmem a) ∧
      ChordListAt c₂.nmem LB (pre ++ collectQ (L.take (j + 1)) (R.take (j + 1))) ∧
      (∀ x, x ≠ 70110 → x ≠ 70114 → x ≠ 70119 → x ≠ ALLOC → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have hc0 : pre ++ collectQ (L.take (j + 1)) (R.take (j + 1)) = C0 ++
        (if r.1 = 1 then [(q.2.1 - 1, r.2.2.1, r.2.2.2)] else []) := by
      rw [htake, htakeL, collectQ_append hlt, hC0, List.append_assoc]
    have hA0 : c.nreg ALLOC = LB + 3 * C0.length := by rw [hI.alloc, hj]
    have h10 : c.nreg 70110 = C0.length := by rw [hI.cnt, hj]
    by_cases hf : r.1 = 1
    · rw [ite_eq_left hf] at hc0
      have hlt1 : c₁.nreg 70108 < c₁.nreg 70114 := by
        rw [v14, q₁ _ (by decide), r08, hf]; omega
      have hlt2 : c₁.nreg 70114 < c₁.nreg 70118 := by
        rw [v14, q₁ _ (by decide), r18, hf]; omega
      set a := LB + 3 * C0.length
      obtain ⟨c₂, k₂, e₂, hk₂, a₂, mo, m0, m1, m2, n10, R₂, rr₂, rm₂, o₂⟩ := clqCopy_exec (P := P)
        c₁ hw₁ (s := RB + 4 * j) (t := QB + 3 * j) (a := a) (K := C0.length)
        (by rw [q₁ _ (by decide), hcur]) (by rw [q₁ _ (by decide), hqcur])
        (by rw [q₁ _ (by decide), hA0]) (by rw [q₁ _ (by decide), r05])
        (by rw [q₁ _ (by decide), r18]) (by rw [q₁ _ (by decide), h10]) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      refine ⟨c₂, _, .ifLtN_true hlt1 (.ifLtN_true hlt2 e₂), by omega, ?_, ?_, fun x hx => ?_,
        ?_, fun x a1 a2 a3 a4 => ?_, by rw [rr₂], by rw [rm₂], by rw [o₂]⟩
      · rw [a₂, hc0, List.length_append, List.length_singleton]; simp only [a]; ring
      · rw [n10, hc0]; simp only [hC0, List.length_append, List.length_singleton]
      · rw [mo x (Or.inl hx)]
      · rw [hc0]
        have hlist := hI.list
        rw [hj] at hlist
        have hl : ChordListAt c₂.nmem LB C0 := fun i hi => by
          obtain ⟨b0, b1, b2⟩ := hlist i hi
          refine ⟨?_, ?_, ?_⟩
          · rwa [mo _ (Or.inl (by omega))]
          · rwa [mo _ (Or.inl (by omega))]
          · rwa [mo _ (Or.inl (by omega))]
        refine chordListAt_append hl ?_ ?_ ?_
        · rw [m0, hqmem, p1]
        · rwa [m1, hmem 2 (by omega)]
        · rwa [m2, hmem 3 (by omega)]
      · rw [R₂ x a1 a2 a3 a4]
        exact q₁ x a2
    · rw [ite_eq_right hf, List.append_nil] at hc0
      have hsk : Exec P W (.ifLtN 70108 70114 (.ifLtN 70114 70118 clqCopy .skip) .skip) c₁ c₁
          (if c₁.nreg 70108 < c₁.nreg 70114 then 0 + 2 + 1 else 0 + 2) := by
        by_cases hlt1 : c₁.nreg 70108 < c₁.nreg 70114
        · rw [ite_eq_left hlt1]
          have hlt2 : ¬ c₁.nreg 70114 < c₁.nreg 70118 := by
            rw [v14, q₁ _ (by decide), r18]
            rw [v14, q₁ _ (by decide), r08] at hlt1; omega
          exact .ifLtN_true hlt1 (.ifLtN_false hlt2 (.skip hw₁))
        · rw [ite_eq_right hlt1]; exact .ifLtN_false hlt1 (.skip hw₁)
      refine ⟨c₁, _, hsk, by split_ifs <;> omega, ?_, ?_, fun x _ => rfl, ?_,
        fun x _ a2 _ _ => q₁ x a2, rfl, rfl, rfl⟩
      · rw [q₁ _ (by decide), hA0, hc0]
      · rw [q₁ _ (by decide), h10, hc0]
      · rw [hc0]; have := hI.list; rwa [hj] at this
  have hw₂ := e₂.wb_right
  have c205 : c₂.nreg 70105 = 1 := (q₂ _ (by decide) (by decide) (by decide) (by decide)).trans r05
  have c216 : c₂.nreg 70116 = 3 := (q₂ _ (by decide) (by decide) (by decide) (by decide)).trans r16
  have c217 : c₂.nreg 70117 = 4 := (q₂ _ (by decide) (by decide) (by decide) (by decide)).trans r17
  have r13 : c₂.nreg 70113 = RB + 4 * j := by
    rw [q₂ _ (by decide) (by decide) (by decide) (by decide), hcur]
  have r15 : c₂.nreg 70115 = QB + 3 * j := by
    rw [q₂ _ (by decide) (by decide) (by decide) (by decide), hqcur]
  have r12 : c₂.nreg 70112 = j := by rw [q₂ _ (by decide) (by decide) (by decide) (by decide), hj]
  obtain ⟨c₃, k₃, e₃, hk₃, u13, u15, u12, u₃, um₃, urr₃, urm₃, uo₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.addN 70113 70113 70117, .addN 70115 70115 70116, .addN 70112 70112 70105]) c₂ c₃ k₃ ∧
      k₃ = 3 ∧ c₃.nreg 70113 = RB + 4 * (j + 1) ∧ c₃.nreg 70115 = QB + 3 * (j + 1) ∧
      c₃.nreg 70112 = j + 1 ∧
      (∀ r, r ≠ 70112 → r ≠ 70113 → r ≠ 70115 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, r13, r15, r12, c205, c216, c217]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r13, r15, r12, c205, c216, c217]
    all_goals ring
  have ex : Exec P W clqBody c c₃ ((1 + 0) + (k₂ + k₃)) :=
    .seq (.seq e₁ (.skip hw₁)) (.seq e₂ e₃)
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, by rw [u13, u12], by rw [u15, u12],
    by rwa [u12, u₃ _ (by decide) (by decide) (by decide)],
    by rwa [u12, u₃ _ (by decide) (by decide) (by decide)],
    fun x a1 a2 a3 a4 a5 a6 a7 => ?_, fun a ha => ?_, by rwa [um₃, u12],
    by rw [urr₃, rr₂, hI.rr], by rw [urm₃, rm₂, hI.rm], by rw [uo₃, o₂, hI.out]⟩,
    by omega, by omega, by rw [u12, hj]⟩
  · rw [u₃ x a2 a3 a5, q₂ x a1 a4 a6 a7, hreg x a1 a2 a3 a4 a5 a6 a7]
  · have : pre.length ≤ C0.length := by rw [hC0, List.length_append]; omega
    rw [um₃, m₂ a (by omega), hI.low a ha]

/-- **The collection loop.** -/
theorem clqLoop_exec {P : Polygon} {W : ℕ} {L : List (ℕ × ℕ × ℕ)} {R : List (ℕ × ℕ × ℕ × ℕ)}
    {QB RB LB : ℕ} {pre : List (ℕ × ℕ × ℕ)} {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70116 = 3)
    (h17 : c₀.nreg 70117 = 4) (h18 : c₀.nreg 70118 = 2) (h11 : c₀.nreg 70111 = R.length)
    (hLR : L.length = R.length)
    (hR : ResultListAt c₀.nmem RB R) (hQ : ChordListAt c₀.nmem QB L)
    (hRB : RB + 4 * R.length ≤ LB) (hQB : QB + 3 * L.length ≤ LB)
    (hW : LB + 3 * pre.length + 3 * R.length + 4 ≤ W) (hWK : pre.length + R.length + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), CLQI W L R QB RB LB pre c₀ c → c.nreg 70112 + n = R.length →
      ∃ c' k, Exec P W clqLoop c c' k ∧ k ≤ 24 * n + 2 ∧ 3 * n ≤ k ∧
        CLQI W L R QB RB LB pre c₀ c' ∧
        c'.nreg 70112 = R.length
  | 0, c, hI, hn => by
    have h11' : c.nreg 70111 = R.length := by
      rw [hI.regs 70111 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h11]
    exact ⟨c, 2, .whileLtN_false (by rw [h11']; omega) hI.wb, by omega, by omega, hI, by omega⟩
  | n + 1, c, hI, hn => by
    have ht : c.nreg 70112 < R.length := by omega
    obtain ⟨c', k, e, hI', hk, hk4, hc'⟩ := clqBody_step (P := P) hI ht h05 h08 h16 h17 h18 hLR hR hQ
      hRB hQB hW hWK
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := clqLoop_exec h05 h08 h16 h17 h18 h11 hLR hR hQ hRB hQB
      hW hWK n c' hI' (by omega)
    have h11' : c.nreg 70111 = R.length := by
      rw [hI.regs 70111 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h11]
    exact ⟨c'', k + 2 + k₂, .whileLtN_true (by rwa [h11']) e e₂, by omega, by omega,
      hI'', hK⟩

end

end FuseAsm

end Chazelle.Core
