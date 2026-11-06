module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FuseAsmQuery
public import Chazelle.Core.MergeAsmProg
public import Chazelle.Core.FuseAsmSet

/-!
# WP-F fusion assembly, part 3: writing the chord-end queries

`qlLoop` reads the `K` chord records at `CB` (five words each: `h, lp, rp, up, dn`) and appends
two queries per chord at the allocator: `(lp, h + 1, 1)` and `(rp, h + 1, 0)` (`endQL`), raising
the allocator by `6` per chord.  Registers (band `bFuse`):

| register | content |
|---|---|
| `70100` | number of chords `K` |
| `70101` | cursor in the chord area |
| `70102` | loop index |
| `70103`, `70104`, `70107` | scratch (`70104 = h + 1`) |
| `70105`, `70106`, `70108` | constants `1`, `5`, `0` |
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK
open Chazelle.Merge (lend rend)

@[expose] public section

/-- The query list of a list of chord records: two queries per record. -/
def endQL (cs : List CRec) : List (ℕ × ℕ × ℕ) :=
  (List.range (2 * cs.length)).map fun j =>
    let r := cs.getD (j / 2) ⟨0, 0, 0, 0, 0⟩
    if j % 2 = 0 then (r.lp, r.h + 1, 1) else (r.rp, r.h + 1, 0)

section
variable (cs : List CRec)
/-- The query list is the one of `SweepSpec` (finding S-1). -/
theorem endQL_eq : endQL cs = sweepEndQ cs := rfl

theorem endQL_length : (endQL cs).length = 2 * cs.length := by
  simp [endQL]

theorem endQL_get {j : ℕ} (hj : j < 2 * cs.length) :
    (endQL cs).getD j (0, 0, 0) =
      let r := cs.getD (j / 2) ⟨0, 0, 0, 0, 0⟩
      if j % 2 = 0 then (r.lp, r.h + 1, 1) else (r.rp, r.h + 1, 0) := by
  grind [endQL, List.getD_eq_getElem?_getD]


end

/-- One chord: two queries. -/
def qlBody : Stmt := block [.loadN 70103 70101, .addN 70104 70103 70105,
  .addN 70107 70101 70105, .loadN 70103 70107,
  .storeN ALLOC 70103, .addN ALLOC ALLOC 70105, .storeN ALLOC 70104, .addN ALLOC ALLOC 70105,
  .storeN ALLOC 70105, .addN ALLOC ALLOC 70105,
  .addN 70107 70107 70105, .loadN 70103 70107,
  .storeN ALLOC 70103, .addN ALLOC ALLOC 70105, .storeN ALLOC 70104, .addN ALLOC ALLOC 70105,
  .storeN ALLOC 70108, .addN ALLOC ALLOC 70105,
  .addN 70101 70101 70106, .addN 70102 70102 70105]

/-- The query loop. -/
def qlLoop : Stmt := .whileLtN 70102 70100 qlBody

set_option maxHeartbeats 4000000 in
theorem qlBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {s a : ℕ}
    (h01 : c.nreg 70101 = s) (hA : c.nreg ALLOC = a) (h05 : c.nreg 70105 = 1)
    (h06 : c.nreg 70106 = 5) (h08 : c.nreg 70108 = 0) (hs : s + 5 ≤ W) (ha : a + 6 ≤ W)
    (hi : c.nreg 70102 + 1 ≤ W) (hh : c.nmem s + 1 ≤ W) (hsa : s + 2 < a) :
    ∃ c' k, Exec P W qlBody c c' k ∧ k = 20 ∧ c'.nreg 70101 = s + 5 ∧ c'.nreg ALLOC = a + 6 ∧
      c'.nreg 70102 = c.nreg 70102 + 1 ∧
      (∀ x, (x < a ∨ a + 6 ≤ x) → c'.nmem x = c.nmem x) ∧
      c'.nmem a = c.nmem (s + 1) ∧ c'.nmem (a + 1) = c.nmem s + 1 ∧ c'.nmem (a + 2) = 1 ∧
      c'.nmem (a + 3) = c.nmem (s + 2) ∧ c'.nmem (a + 4) = c.nmem s + 1 ∧ c'.nmem (a + 5) = 0 ∧
      (∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold qlBody
  have hA' : c.nreg 9999 = a := hA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h01, hA', h05, h06, h08, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h01, hA', h05, h06, h08, ALLOC])
  · have a6' : r ≠ 9999 := a6
    simp (disch := omega) only [Machine.upd_other]

/-- The invariant of the query loop. -/
structure QLI (W K CB LB : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 70102 ≤ K
  cur : c.nreg 70101 = CB + 5 * c.nreg 70102
  alloc : c.nreg ALLOC = LB + 6 * c.nreg 70102
  regs : ∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
    c.nreg r = c₀.nreg r
  low : ∀ a, a < LB → c.nmem a = c₀.nmem a
  done : ∀ i, i < c.nreg 70102 →
    c.nmem (LB + 6 * i) = c₀.nmem (CB + 5 * i + 1) ∧
    c.nmem (LB + 6 * i + 1) = c₀.nmem (CB + 5 * i) + 1 ∧ c.nmem (LB + 6 * i + 2) = 1 ∧
    c.nmem (LB + 6 * i + 3) = c₀.nmem (CB + 5 * i + 2) ∧
    c.nmem (LB + 6 * i + 4) = c₀.nmem (CB + 5 * i) + 1 ∧ c.nmem (LB + 6 * i + 5) = 0
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 4000000 in
/-- **The query loop.** -/
theorem qlLoop_exec {P : Polygon} {W K CB LB : ℕ} {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h06 : c₀.nreg 70106 = 5) (h08 : c₀.nreg 70108 = 0)
    (h00 : c₀.nreg 70100 = K) (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB)
    (hh : ∀ i, i < K → c₀.nmem (CB + 5 * i) + 1 ≤ W) (hW : LB + 6 * K ≤ W) (hWK : K + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), QLI W K CB LB c₀ c → c.nreg 70102 + n = K →
      ∃ c' k, Exec P W qlLoop c c' k ∧ k ≤ 22 * n + 2 ∧ 6 * n ≤ k ∧ QLI W K CB LB c₀ c' ∧
        c'.nreg 70102 = K
  | 0, c, hI, hn => ⟨c, 2, .whileLtN_false (by rw [hI.regs 70100 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h00]; omega) hI.wb, by omega, by omega, hI,
      by omega⟩
  | n + 1, c, hI, hn => by
    obtain ⟨i, hi⟩ : ∃ i, c.nreg 70102 = i := ⟨_, rfl⟩
    have hiK : i < K := by omega
    have hCBi := hCB i hiK
    have hmem : c.nmem (CB + 5 * i) = c₀.nmem (CB + 5 * i) := hI.low _ (by omega)
    obtain ⟨c', k, e, hk, v01, vA, v02, mo, m0, m1, m2, m3, m4, m5, R, rr, rm, ro⟩ :=
      qlBody_exec (P := P) c hI.wb (by rw [hI.cur, hi]) (by rw [hI.alloc, hi])
        (by rw [hI.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h05])
        (by rw [hI.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h06])
        (by rw [hI.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h08])
        (by omega) (by omega) (by omega) (by simp_all) (by omega)
    rw [hi] at v02
    have hI' : QLI W K CB LB c₀ c' := by
      refine ⟨e.wb_right, by omega, by omega, by omega,
        fun r a1 a2 a3 a4 a5 a6 => by rw [R r a1 a2 a3 a4 a5 a6, hI.regs r a1 a2 a3 a4 a5 a6],
        fun a ha => by rw [mo a (Or.inl (by omega)), hI.low a ha], fun i' hi' => ?_,
        by rw [rr, hI.rr], by rw [rm, hI.rm], by rw [ro, hI.out]⟩
      rw [v02] at hi'
      rcases Nat.lt_or_ge i' i with hlt | hge
      all_goals (grind [Chazelle.Core.FuseAsm.QLI.done, Chazelle.Core.FuseAsm.QLI.low])
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := qlLoop_exec h05 h06 h08 h00 hCB hh hW hWK n c'
      hI' (by omega)
    exact ⟨c'', k + 2 + k₂, .whileLtN_true (by
      rw [hi, hI.regs 70100 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h00]; exact hiK) e e₂, by omega, by omega, hI'', hK⟩

/-- **The written query list.** -/
theorem chordList_endQL {m m₀ : ℕ → ℕ} {LB CB : ℕ} {cs : List CRec}
    (hcs : ∀ i, i < cs.length → m₀ (CB + 5 * i) = (cs.getD i ⟨0, 0, 0, 0, 0⟩).h ∧
      m₀ (CB + 5 * i + 1) = (cs.getD i ⟨0, 0, 0, 0, 0⟩).lp ∧
      m₀ (CB + 5 * i + 2) = (cs.getD i ⟨0, 0, 0, 0, 0⟩).rp)
    (hdone : ∀ i, i < cs.length →
      m (LB + 6 * i) = m₀ (CB + 5 * i + 1) ∧ m (LB + 6 * i + 1) = m₀ (CB + 5 * i) + 1 ∧
      m (LB + 6 * i + 2) = 1 ∧ m (LB + 6 * i + 3) = m₀ (CB + 5 * i + 2) ∧
      m (LB + 6 * i + 4) = m₀ (CB + 5 * i) + 1 ∧ m (LB + 6 * i + 5) = 0) :
    ChordListAt m LB (endQL cs) := by
  intro j hj
  rw [endQL_length] at hj
  rw [endQL_get cs hj]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  all_goals ram_grind

/-- **The chord-end queries of a normal form** are valid and ask exactly the chord ends. -/
theorem endQL_ok (J : Merge.Junction) (Q : Polygon) (i : ℕ) {N : NF}
    (hN : IsNF (chainModel (sideChain J i)) Q N) :
    (∀ q ∈ endQL N.chords, QueryOK J Q i q) ∧
      geoQ J Q i (endQL N.chords) = endQ (N.F (chainModel (sideChain J i)) Q) := by
  set M := chainModel (sideChain J i)
  obtain ⟨-, -, -, -, -, -, -, -, -, hhQ, -⟩ := id hN
  have memk : ∀ k, k < N.chords.length → N.chord k ∈ N.chords := fun k hk => by
    simp_all [NF.chord] 
  have key : ∀ k, k < N.chords.length →
      QueryOK J Q i ((N.chord k).lp, (N.chord k).h + 1, 1) ∧
        QueryOK J Q i ((N.chord k).rp, (N.chord k).h + 1, 0) ∧
        M.pos Q (N.chord k).lpos = lend ((N.chord k).toSet M Q) ∧
        M.pos Q (N.chord k).rpos = rend ((N.chord k).toSet M Q) := fun k hk =>
    queryOK_ends J Q i (N.chord k) (hN.2.2.1 k hk)
      (hN.1.2.1 ⟨N.chord k, memk k hk, rfl⟩)
      (hhQ k hk)
  have mem : ∀ q, q ∈ endQL N.chords ↔ ∃ k, k < N.chords.length ∧
      (q = ((N.chord k).lp, (N.chord k).h + 1, 1) ∨ q = ((N.chord k).rp, (N.chord k).h + 1, 0)) := by
    intro q
    simp only [endQL, List.mem_map, List.mem_range, NF.chord]
    constructor
    · grind
    · rintro ⟨k, hk, rfl | rfl⟩
      · exact ⟨2 * k, by omega, by simp⟩
      · exact ⟨2 * k + 1, by omega, by
          grind⟩
  refine ⟨fun q hq => ?_, ?_⟩
  · grind
  · ext x
    simp only [geoQ, endQ, NF.F, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨k, hk, rfl | rfl⟩ := (mem q).1 hq
      · left
        refine ⟨_, ⟨N.chord k, memk k hk, rfl⟩, ?_⟩
        show (M.pos Q (N.chord k).lpos, dirOf 1) = _
        grind [dirOf]
      · right
        refine ⟨_, ⟨N.chord k, memk k hk, rfl⟩, ?_⟩
        show (M.pos Q (N.chord k).rpos, dirOf 0) = _
        grind [dirOf]
    · rintro (⟨c, ⟨r, hr, rfl⟩, rfl⟩ | ⟨c, ⟨r, hr, rfl⟩, rfl⟩)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        have hck : N.chord k = N.chords[k] := by grind [NF.chord]
        refine ⟨_, (mem _).2 ⟨k, hk, Or.inl rfl⟩, ?_⟩
        show (lend (N.chords[k].toSet M Q), 1) = (M.pos Q (N.chord k).lpos, dirOf 1)
        grind [dirOf]
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        have hck : N.chord k = N.chords[k] := by grind [NF.chord]
        refine ⟨_, (mem _).2 ⟨k, hk, Or.inr rfl⟩, ?_⟩
        show (rend (N.chords[k].toSet M Q), -1) = (M.pos Q (N.chord k).rpos, dirOf 0)
        grind [dirOf]

end

end FuseAsm

end Chazelle.Core
