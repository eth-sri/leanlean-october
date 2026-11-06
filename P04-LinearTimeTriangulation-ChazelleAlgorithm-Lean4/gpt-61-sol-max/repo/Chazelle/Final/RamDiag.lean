module

public meta import Chazelle.Arithmetic

public import Chazelle.Final.RamSplit
public import Chazelle.Core.SpecRam
public import Mathlib.Data.List.GetD

/-!
# Computing the diagonal list on the RAM

`diagStmt` computes, from the trapezoid table and the vertex-chord table in memory, a list `E`
of the inserted diagonals, each exactly once as an unordered pair (smaller index first), in time
linear in the sizes of the tables: `E` is a permutation of `diagList Q T C`
(`Chazelle.Final.Interface`).

## Deduplication without hashing

The candidate pairs (`trapPairs` followed by `chordPairs`) are normalised (`sortPair`) and
inserted one by one (`ins`): a pair `(lo, hi)` is appended to `E` unless it is already there.
Membership is tested by scanning the members of `E` with first entry `lo`, which are chained
through a sibling array from a head array indexed by vertex (`idx`).  By the degree bound
(`countP_diagList_le`, at most `10` inserted diagonals per vertex) a scan costs `O(1)`.

## Layout

Inputs (natural registers, never written): `nreg 200 = DB` (the output band: pair `j` at
`DB + 2j, DB + 2j + 1`), `nreg 201 = HB` (the head array, `n` cells), `nreg 202 = SB` (the
sibling array); the hand-off registers `9990 … 9993` (`Chazelle.Core.REG_TRAP` …).
Registers written: natural `203 … 227`; the number of pairs is left in `nreg 206`.
Memory written: `[DB, SB + |T| + |C|)`.
-/

namespace Chazelle.Final

open Machine Machine.Stmt Programs

@[expose] public section

/-! ### The abstract insertion -/

/-- Insert the normal form of `d` into `E` unless it is already a member. -/
def ins (E : List (ℕ × ℕ)) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  if sortPair d ∈ E then E else E ++ [sortPair d]

/-- The positions (offset by `o`, increasing) of the members of `E` with first entry `v`. -/
def idx : List (ℕ × ℕ) → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | e :: E, v, o => if e.1 = v then o :: idx E v (o + 1) else idx E v (o + 1)

section
variable (E : List (ℕ × ℕ))
/-- Appending a pair appends its position when its first entry is `v`. -/
theorem idx_append_single (p : ℕ × ℕ) (v o : ℕ) :
    idx (E ++ [p]) v o = idx E v o ++ (if p.1 = v then [o + E.length] else []) := by
  induction E generalizing o with
  | nil => simp [idx]
  | cons e E ih =>
    core_grind

/-- The positions listed by `idx E v o` are exactly the offset positions with first entry `v`. -/
theorem mem_idx (v : ℕ) : ∀ (o j : ℕ), j ∈ idx E v o ↔
    o ≤ j ∧ j < o + E.length ∧ (E.getD (j - o) (0, 0)).1 = v := by
  induction E with
  | nil => simp_all [idx, List.not_mem_nil, List.length_nil, false_iff]
  | cons e E ih =>
    intro o j
    simp only [idx, List.length_cons]
    have key : j ∈ idx E v (o + 1) ↔ o + 1 ≤ j ∧ j < o + (E.length + 1) ∧
        ((e :: E).getD (j - o) (0, 0)).1 = v := by
      rw [ih]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, by omega, ?_⟩
        rw [show j - o = (j - (o + 1)) + 1 by omega]
        grind
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, by omega, ?_⟩
        rw [show j - o = (j - (o + 1)) + 1 by omega] at h3
        grind
    split_ifs with he
    · rw [List.mem_cons, key]
      constructor
      · rintro (rfl | h)
        all_goals grind
      omega
    · rw [key]
      constructor
      · omega
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        by_contra hj
        simp_all

/-- The number of positions with first entry `v` is the corresponding count. -/
theorem length_idx (v : ℕ) : ∀ o,
    (idx E v o).length = E.countP (fun e => decide (e.1 = v)) := by
  induction E with
  | nil => intro o; rfl
  | cons e E ih =>
    core_grind


end

/-- Listed positions are positions of the list. -/
theorem idx_lt {E : List (ℕ × ℕ)} {v j : ℕ} (h : j ∈ idx E v 0) : j < E.length := by
  have := ((mem_idx E v 0 j).1 h).2.1
  omega

/-- A pair `(lo, hi)` is a member iff a position with first entry `lo` holds `hi`. -/
theorem mem_iff_idx (E : List (ℕ × ℕ)) (lo hi : ℕ) :
    (lo, hi) ∈ E ↔ ∃ j ∈ idx E lo 0, (E.getD j (0, 0)).2 = hi := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    refine ⟨j, (mem_idx E lo 0 j).2 ⟨Nat.zero_le _, by omega, ?_⟩, ?_⟩
    all_goals simp_all
  grind [Chazelle.Final.mem_idx]

/-! ### Properties of repeated insertion -/

section
variable {E : List (ℕ × ℕ)}
theorem ins_nodup (h : E.Nodup) (d : ℕ × ℕ) : (ins E d).Nodup := by
  unfold ins
  grind

/-- The members after an insertion. -/
theorem mem_ins {d x : ℕ × ℕ} : x ∈ ins E d ↔ x ∈ E ∨ x = sortPair d := by
  grind [ins, List.mem_append, List.mem_singleton]


end

/-- An insertion adds at most one member. -/
theorem length_ins_le (E : List (ℕ × ℕ)) (d : ℕ × ℕ) : (ins E d).length ≤ E.length + 1 := by
  grind [ins]

section
variable (L : List (ℕ × ℕ))
/-- Repeated insertion keeps a list duplicate-free. -/
theorem foldl_ins_nodup : ∀ E : List (ℕ × ℕ), E.Nodup →
    (L.foldl ins E).Nodup := by
  induction L with
  | nil => simp_all
  | cons d L ih => intro E h; exact ih _ (ins_nodup h d)

/-- The members after repeated insertion: the old ones and the normal forms of the inserted pairs. -/
theorem mem_foldl_ins : ∀ (E : List (ℕ × ℕ)) (x : ℕ × ℕ),
    x ∈ L.foldl ins E ↔ x ∈ E ∨ ∃ e ∈ L, sortPair e = x := by
  induction L with
  | nil => simp_all
  | cons d L ih =>
    intro E x
    rw [List.foldl_cons, ih, mem_ins]
    grind

/-- Repeated insertion adds at most one member per inserted pair. -/
theorem length_foldl_ins_le : ∀ E : List (ℕ × ℕ),
    (L.foldl ins E).length ≤ E.length + L.length := by
  induction L with
  | nil => simp_all
  | cons d L ih =>
    intro E
    rw [List.foldl_cons, List.length_cons]
    have := ih (ins E d)
    have := length_ins_le E d
    omega


end

/-- **The result of the insertions is a permutation of `diagList`.** -/
theorem foldl_ins_perm {Q : Polygon} (T : TrapTable) (C : List ChordRec) :
    ((trapPairs Q T ++ chordPairs C).foldl ins []).Perm (diagList Q T C) := by
  rw [List.perm_ext_iff_of_nodup (foldl_ins_nodup _ _ List.nodup_nil) (diagList_nodup Q T C)]
  simp_all [mem_foldl_ins, diagList, List.mem_dedup, List.mem_map]

/-- **Degree bound for partial insertions**: at most `10` members with first entry `v`. -/
theorem countP_foldl_ins_le {Q : Polygon} (hQ : Q.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {L : List (ℕ × ℕ)}
    (hL : ∀ e ∈ L, e ∈ trapPairs Q T ++ chordPairs C) (v : ℕ) :
    (L.foldl ins []).countP (fun e => decide (e.1 = v)) ≤ 10 := by
  have hnd := foldl_ins_nodup L [] List.nodup_nil
  have hsub : L.foldl ins [] ⊆ diagList Q T C := by
    grind [mem_foldl_ins, diagList, List.mem_dedup, List.mem_map]
  calc (L.foldl ins []).countP (fun e => decide (e.1 = v))
      ≤ (diagList Q T C).countP (fun e => decide (e.1 = v)) :=
        (List.subperm_of_subset hnd hsub).countP_le _
    _ ≤ (diagList Q T C).countP (fun d => decide (d.1 = v ∨ d.2 = v)) :=
        List.countP_mono_left fun x _ h => by
          simp_all
    _ ≤ 10 := countP_diagList_le hQ hT hC v

/-- The trapezoid pairs of a prefix grow by at most one pair per record. -/
theorem trapPairs_take_succ (Q : Polygon) {T : TrapTable} {j : ℕ} (hj : j < T.length) :
    trapPairs Q (T.take (j + 1)) = trapPairs Q (T.take j) ++
      (if TrapRec.nonAdj Q.n T[j] then [(T[j].top, T[j].bot)] else []) := by
  grind [trapPairs, List.take_add_one, Option.toList_some, List.filter_append, List.map_append, List.filter_cons, List.filter_nil]

/-- The chord pairs of a prefix grow by one pair per record. -/
theorem chordPairs_take_succ {C : List ChordRec} {j : ℕ} (hj : j < C.length) :
    chordPairs (C.take (j + 1)) = chordPairs (C.take j) ++ [(C[j].src, C[j].dst)] := by
  grind [chordPairs, List.take_add_one, Option.toList_some, List.map_append]

/-- The trapezoid pairs of a prefix are trapezoid pairs. -/
theorem trapPairs_sub (Q : Polygon) (T : TrapTable) (j : ℕ) :
    ∀ e ∈ trapPairs Q (T.take j), e ∈ trapPairs Q T := by
  grind [trapPairs, List.mem_filter]

/-- The chord pairs of a prefix are chord pairs. -/
theorem chordPairs_sub (C : List ChordRec) (j : ℕ) :
    ∀ e ∈ chordPairs (C.take j), e ∈ chordPairs C := by
  core_grind

/-- A prefix of `j` records has at most `j` trapezoid pairs. -/
theorem length_trapPairs_take_le (Q : Polygon) (T : TrapTable) (j : ℕ) :
    (trapPairs Q (T.take j)).length ≤ j := by
  unfold trapPairs
  grind

/-- A prefix of `j` records has at most `j` chord pairs. -/
theorem length_chordPairs_take_le (C : List ChordRec) (j : ℕ) :
    (chordPairs (C.take j)).length ≤ j := by
  simp_all [chordPairs, List.length_map]

/-! ### The memory relation -/

/-- `mem` holds `E`: pair `j` at `DB + 2j`, `DB + 2j + 1`, and for each vertex `v < n` the
positions of the members with first entry `v` (most recent first) chained through the sibling
array `SB` from the head `HB + v`. -/
structure DRel (mem : ℕ → ℕ) (DB HB SB n : ℕ) (E : List (ℕ × ℕ)) : Prop where
  band : ∀ j < E.length, mem (DB + 2 * j) = (E.getD j (0, 0)).1 ∧
    mem (DB + 2 * j + 1) = (E.getD j (0, 0)).2
  chain : ∀ v < n, Chain mem SB (mem (HB + v)) (idx E v 0).reverse

/-! ### The insertion on the RAM -/

/-- One step of the scan: `node := e - 1`; if `D[node].2 = hi` then `found := 1`;
`e := sib[node]`. -/
def scanBody : Stmt :=
  .seq (block [.subN 217 216 205, .addN 218 200 217, .addN 218 218 217, .addN 218 218 205,
      .loadN 219 218])
    (.seq (.ifLtN 219 214 .skip (.ifLtN 214 219 .skip (.instr (.constN 215 1))))
      (block [.addN 218 202 217, .loadN 216 218]))

/-- The scan of the pairs with first entry `lo`. -/
def scanLoop : Stmt := .whileLtN 204 216 scanBody

/-- Append `(lo, hi)`: `D[ND] := (lo, hi)`, `sib[ND] := head[lo]`, `head[lo] := ND + 1`,
`ND := ND + 1`. -/
def emitBlock : Stmt :=
  block [.addN 218 200 206, .addN 218 218 206, .storeN 218 213, .addN 218 218 205,
    .storeN 218 214, .addN 218 201 213, .loadN 219 218, .addN 217 202 206, .storeN 217 219,
    .addN 219 206 205, .storeN 218 219, .copyN 206 219]

/-- **Insert** the pair `(a, b) = (nreg 211, nreg 212)`: normalise, scan, append if new. -/
def insStmt : Stmt :=
  .seq (block [.copyN 213 211, .copyN 214 212])
    (.seq (.ifLtN 212 211 (block [.copyN 213 212, .copyN 214 211]) .skip)
      (.seq (block [.constN 215 0, .addN 218 201 213, .loadN 216 218])
        (.seq scanLoop (.ifLtN 215 205 emitBlock .skip))))

section Ins

variable {P : Polygon} {W : ℕ}

/-- The invariant of the scan. -/
def ScanInvD (W _DB SB : ℕ) (E : List (ℕ × ℕ)) (lo hi : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ (∀ r, (r < 215 ∨ 219 < r) → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧
    ∃ done rest, (idx E lo 0).reverse = done ++ rest ∧ Chain c.nmem SB (c.nreg 216) rest ∧
      (c.nreg 215 = 0 ∨ c.nreg 215 = 1) ∧
      (c.nreg 215 = 1 ↔ ∃ j ∈ done, (E.getD j (0, 0)).2 = hi)

/-- One iteration of the membership scan preserves `ScanInvD` and shortens the remaining chain. -/
theorem scanBody_inv {DB HB SB n : ℕ} {E : List (ℕ × ℕ)} {lo hi : ℕ} {c₀ c : Config}
    (hD : DRel c₀.nmem DB HB SB n E) (h200 : c₀.nreg 200 = DB) (h202 : c₀.nreg 202 = SB)
    (h204 : c₀.nreg 204 = 0) (h205 : c₀.nreg 205 = 1) (h214 : c₀.nreg 214 = hi)
    (hW1 : DB + 2 * E.length ≤ W) (hW2 : SB + E.length ≤ W)
    (hI : ScanInvD W DB SB E lo hi c₀ c) (ht : c.nreg 204 < c.nreg 216) :
    ∃ c' k, Exec P W scanBody c c' k ∧ ScanInvD W DB SB E lo hi c₀ c' ∧ k ≤ 12 ∧
      chainLen c₀.nmem SB (c'.nreg 216) < chainLen c₀.nmem SB (c.nreg 216) := by
  obtain ⟨hw, hfn, hfr, hnm, hrm, hout, done, rest, hsplit, hchain, h01, hfound⟩ := hI
  have e200 : c.nreg 200 = DB := by simp_all
  have e202 : c.nreg 202 = SB := by simp_all
  have e204 : c.nreg 204 = 0 := by simp_all
  have e205 : c.nreg 205 = 1 := by simp_all
  have e214 : c.nreg 214 = hi := by simp_all
  rw [e204] at ht
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    cases rest with
    | nil => grind [Chain]
    | cons z rest' => simp_all
  obtain ⟨he, hchain'⟩ := hchain
  have hzmem : z ∈ idx E lo 0 := by
    simp_all
  have hz : z < E.length := idx_lt hzmem
  have hb := hD.band z hz
  rw [← hnm] at hb
  have hnode : c.nreg 216 - c.nreg 205 = z := by omega
  unfold scanBody
  refine spec_seq ?_
  exec_block
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  have ex : c.nmem (c.nreg 200 + (c.nreg 216 - c.nreg 205) + (c.nreg 216 - c.nreg 205) +
      c.nreg 205) = (E.getD z (0, 0)).2 := by
    grind
  -- the comparison
  have hcmp : ∀ c₁ : Config, WordsBounded W c₁ →
      ∃ c₂ k₂, Exec P W (.ifLtN 219 214 .skip (.ifLtN 214 219 .skip (.instr (.constN 215 1))))
        c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
        c₂.nreg 215 = (if c₁.nreg 219 = c₁.nreg 214 then 1 else c₁.nreg 215) ∧
        (∀ r, r ≠ 215 → c₂.nreg r = c₁.nreg r) ∧ c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧
        c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    intro c₁ hw₁
    by_cases h1 : c₁.nreg 219 < c₁.nreg 214
    · refine spec_ifLtN_true h1 (spec_skip hw₁ ?_)
      grind
    · refine spec_ifLtN_false h1 ?_
      by_cases h2 : c₁.nreg 214 < c₁.nreg 219
      · refine spec_ifLtN_true h2 (spec_skip hw₁ ?_)
        grind
      · refine spec_ifLtN_false h2 (spec_instr (Exec.constN hw₁ 215 1 (by
          omega)) fun _ => ?_)
        refine ⟨by omega, by rw [ite_eq_left (by omega)]; simp, fun r hr => by simp [hr], rfl, rfl,
          rfl, rfl⟩
  refine spec_seq (spec_use (hcmp _ ‹_›) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h215₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at h215₂
  rw [ex, e214] at h215₂
  have e202₂ : c₂.nreg 202 = SB := by ram_simp
  have e217₂ : c₂.nreg 217 = z := by rw [hfn₂ 217 (by decide)]; config_simp; exact hnode
  exec_block
  · omega
  have hmem₂ : c₂.nmem = c.nmem := by rw [hnm₂]
  refine ⟨⟨‹_›, fun r hr => ?_, ?_, ?_, ?_, ?_, done ++ [z], rest', by grind, ?_, ?_,
    ?_⟩, by omega, ?_⟩
  · config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hfn₂ r (by omega)]
    config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), hfn r hr]
  · grind
  · grind
  · grind
  · grind
  · config_simp; grind
  · config_simp
    grind
  · config_simp
    grind
  · config_simp
    rw [hmem₂, e202₂, e217₂]
    have e1 : chainLen c₀.nmem SB (c.nmem (SB + z)) = rest'.length :=
      chainLen_eq (by grind)
    have e2 : chainLen c₀.nmem SB (c.nreg 216) = rest'.length + 1 := by
      rw [chainLen_eq (l := z :: rest') (by grind [Chazelle.Final.Chain])]; simp
    omega

/-- **Appending a new pair preserves the memory relation.** -/
theorem dRel_emit {mem : ℕ → ℕ} {DB HB SB n : ℕ} {E : List (ℕ × ℕ)} {lo hi : ℕ}
    (hD : DRel mem DB HB SB n E) (hlo : lo < n) (hl1 : DB + 2 * (E.length + 1) ≤ HB)
    (hl2 : HB + n ≤ SB) :
    DRel (upd (upd (upd (upd mem (DB + E.length + E.length) lo) (DB + E.length + E.length + 1) hi)
      (SB + E.length) (mem (HB + lo))) (HB + lo) (E.length + 1)) DB HB SB n (E ++ [(lo, hi)]) := by
  set L := E.length with hL
  refine ⟨fun j hj => ?_, fun v hv => ?_⟩
  · rw [List.length_append, List.length_singleton] at hj
    simp only [Machine.upd_apply]
    by_cases hjL : j = L
    · grind
    · have hj' : j < L := by omega
      ram_grind
  · have hsib : ∀ z ∈ (idx E v 0).reverse, upd (upd (upd (upd mem (DB + L + L) lo)
        (DB + L + L + 1) hi) (SB + L) (mem (HB + lo))) (HB + lo) (L + 1) (SB + z) =
        mem (SB + z) := by
      intro z hz
      have := idx_lt (List.mem_reverse.1 hz)
      core_grind
    have hc := chain_congr hsib (hD.chain v hv)
    rw [idx_append_single]
    by_cases hvl : v = lo
    · subst hvl
      rw [ite_eq_left rfl, Nat.zero_add, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      core_grind
    core_grind

section
variable {DB HB SB n : ℕ} {E : List (ℕ × ℕ)}
/-- **Spec of the append block.** -/
theorem emitBlock_exec {lo hi : ℕ} (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h205 : c.nreg 205 = 1) (h206 : c.nreg 206 = E.length)
    (h213 : c.nreg 213 = lo) (h214 : c.nreg 214 = hi) (hlo : lo < n)
    (hD : DRel c.nmem DB HB SB n E) (hl1 : DB + 2 * (E.length + 1) ≤ HB) (hl2 : HB + n ≤ SB)
    (hW : SB + E.length + 1 ≤ W) :
    ∃ c' k, Exec P W emitBlock c c' k ∧ k ≤ 12 ∧ DRel c'.nmem DB HB SB n (E ++ [(lo, hi)]) ∧
      c'.nreg 206 = E.length + 1 ∧
      (∀ r, r ≠ 206 → r ≠ 217 → r ≠ 218 → r ≠ 219 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      (∀ t, (t < DB ∨ SB + E.length + 1 ≤ t) → c'.nmem t = c.nmem t) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold emitBlock
  exec_block
  all_goals first
    | (config_simp; omega)
    | skip
  have hm : upd (upd (upd (upd c.nmem (DB + E.length + E.length) lo)
      (DB + E.length + E.length + 1) hi) (SB + E.length)
      (upd (upd c.nmem (DB + E.length + E.length) lo) (DB + E.length + E.length + 1) hi
        (HB + lo))) (HB + lo) (E.length + 1) =
      upd (upd (upd (upd c.nmem (DB + E.length + E.length) lo) (DB + E.length + E.length + 1) hi)
        (SB + E.length) (c.nmem (HB + lo))) (HB + lo) (E.length + 1) := by
    grind [Machine.upd_apply]
  refine ⟨by omega, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, fun t ht => ?_, rfl, rfl⟩
  · config_simp
    simp only [h200, h201, h202, h205, h206, h213, h214]
    rw [hm]
    exact dRel_emit hD hlo hl1 hl2
  all_goals (grind [Machine.upd_apply])

/-- **Spec of the insertion.**  From a configuration holding `E` (`DRel`, `nreg 206 = |E|`)
and the pair `(a, b) = (nreg 211, nreg 212)` of vertices `< n`, `insStmt` leaves `ins E (a, b)`,
at cost `≤ 14 * (number of members of E with first entry min a b) + 26`. -/
theorem insStmt_exec {a b : ℕ} (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h204 : c.nreg 204 = 0) (h205 : c.nreg 205 = 1)
    (h206 : c.nreg 206 = E.length) (h211 : c.nreg 211 = a) (h212 : c.nreg 212 = b)
    (ha : a < n) (hb : b < n) (hD : DRel c.nmem DB HB SB n E)
    (hl1 : DB + 2 * (E.length + 1) ≤ HB) (hl2 : HB + n ≤ SB) (hW : SB + E.length + 1 ≤ W) :
    ∃ c' k, Exec P W insStmt c c' k ∧
      k ≤ 14 * E.countP (fun e => decide (e.1 = min a b)) + 26 ∧
      DRel c'.nmem DB HB SB n (ins E (a, b)) ∧ c'.nreg 206 = (ins E (a, b)).length ∧
      (∀ r, r ≠ 206 → (r < 213 ∨ 219 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      (∀ t, (t < DB ∨ SB + E.length + 1 ≤ t) → c'.nmem t = c.nmem t) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold insStmt scanLoop
  refine spec_seq ?_
  exec_block
  -- normalise
  have hsort : ∃ c₂ k₂, Exec P W (.ifLtN 212 211 (block [.copyN 213 212, .copyN 214 211]) .skip)
      { c with nreg := upd (upd c.nreg 213 (c.nreg 211)) 214 (c.nreg 212) } c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 213 = min a b ∧ c₂.nreg 214 = max a b ∧
      (∀ r, r ≠ 213 → r ≠ 214 → c₂.nreg r = c.nreg r) ∧ c₂.rreg = c.rreg ∧ c₂.nmem = c.nmem ∧
      c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hab : b < a
    · refine spec_ifLtN_true (by simp_all) ?_
      exec_block
      simp_all +zetaDelta <;> omega
    · refine spec_ifLtN_false (by simp_all) (spec_skip
        (by assumption) ?_)
      simp_all
  refine spec_seq (spec_use hsort ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h213₂, h214₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  set lo := min a b with hlo
  set hi := max a b with hhi
  have hlon : lo < n := by omega
  
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; grind
  refine spec_name fun c₃ hc₃ => ?_
  have hw₃ : WordsBounded W c₃ := by grind
  have hmem₃ : c₃.nmem = c.nmem := by grind
  have hreg₃ : ∀ r, r ≠ 213 → r ≠ 214 → r ≠ 215 → r ≠ 216 → r ≠ 218 → c₃.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4 a5
    rw [hc₃]; ram_simp
  have e200 : c₃.nreg 200 = DB := by grind
  have e202 : c₃.nreg 202 = SB := by grind
  have e204 : c₃.nreg 204 = 0 := by grind
  have e205 : c₃.nreg 205 = 1 := by grind
  have e213 : c₃.nreg 213 = lo := by rw [hc₃]; config_simp; exact h213₂
  have e214 : c₃.nreg 214 = hi := by rw [hc₃]; config_simp; exact h214₂
  have hlen : (idx E lo 0).length = E.countP (fun e => decide (e.1 = lo)) := length_idx E lo 0
  have hch₃ : Chain c₃.nmem SB (c₃.nreg 216) (idx E lo 0).reverse := by
    have := hD.chain lo hlon
    rw [hmem₃]
    have e : c₃.nreg 216 = c.nmem (HB + lo) := by
      rw [hc₃]; config_simp; grind
    ram_grind
  have hI₀ : ScanInvD W DB SB E lo hi c₃ c₃ := by
    refine ⟨hw₃, fun _ _ => rfl, rfl, rfl, rfl, rfl, [], (idx E lo 0).reverse, rfl, hch₃, ?_, ?_⟩
    · left; rw [hc₃]; config_simp
    · rw [hc₃]; config_simp; simp
  have hW1 : DB + 2 * E.length ≤ W := by omega
  have hW2 : SB + E.length ≤ W := by omega
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄, done, rest, hsplit, hchain, h01,
    hfound⟩, hexit, hk₄⟩ := Exec.whileLtN_bounded (P := P) (ScanInvD W DB SB E lo hi c₃)
    (fun d => chainLen c₃.nmem SB (d.nreg 216)) 12 (fun _ h => h.1)
    (fun d hd ht => scanBody_inv (hmem₃ ▸ hD) e200 e202 e204 e205 e214 hW1 hW2 hd ht) hI₀
  refine spec_seq ⟨c₄, k₄, ex₄, ?_⟩
  have hrest : rest = [] := by
    have e : c₄.nreg 204 = 0 := by grind
    rw [e] at hexit
    cases rest with
    | nil => rfl
    | cons z l => exact absurd (by ram_grind) hexit
  subst hrest
  rw [List.append_nil] at hsplit
  have hμ : chainLen c₃.nmem SB (c₃.nreg 216) = E.countP (fun e => decide (e.1 = lo)) := by
    rw [chainLen_eq hch₃, List.length_reverse, hlen]
  have hmemb : c₄.nreg 215 = 1 ↔ (lo, hi) ∈ E := by
    rw [hfound, mem_iff_idx, ← hsplit]
    simp only [List.mem_reverse]
  have hmem₄ : c₄.nmem = c.nmem := by ram_grind
  have hreg₄ : ∀ r, (r < 213 ∨ 219 < r) → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hfn₄ r (by omega), hreg₃ r (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hsp : sortPair (a, b) = (lo, hi) := rfl
  by_cases hin : (lo, hi) ∈ E
  · -- already present: skip
    
    refine spec_ifLtN_false (by grind) (spec_skip hw₄ ?_)
    have hins : ins E (a, b) = E := by grind [ins]
    rw [hins]
    refine ⟨?_, by ram_grind, by grind, fun r _ hr => hreg₄ r hr,
      by grind, fun t _ => by rw [hmem₄],
      by grind, by grind⟩
    omega
  · 
    refine spec_ifLtN_true (by grind) ?_
    refine spec_use (emitBlock_exec (P := P) (n := n) (E := E) (lo := lo) (hi := hi) c₄ hw₄
      (by grind) (by grind)
      (by grind) (by grind)
      (by grind) (by grind)
      (by grind) hlon (by ram_grind) hl1 hl2 hW) ?_
    grind [ins, List.length_append, List.length_singleton]


end

end Ins

/-! ### Small kernels -/

/-- `nreg r := 1` if `nreg a ≠ nreg b`, else `0`. -/
def neqFlag (r a b : ℕ) : Stmt :=
  .seq (.instr (.constN r 1)) (.ifLtN a b .skip (.ifLtN b a .skip (.instr (.constN r 0))))

/-- `nreg r := 0` unless `nreg r < nreg m`. -/
def wrapZero (r m : ℕ) : Stmt := .ifLtN r m .skip (.instr (.constN r 0))

section Kernels

variable {P : Polygon} {W : ℕ}

/-- Spec of `neqFlag`: cost `≤ 6`, `nreg r = 0` iff `nreg a = nreg b` (else `1`). -/
theorem neqFlag_exec (r a b : ℕ) (hra : r ≠ a) (hrb : r ≠ b) (c : Config) (hc : WordsBounded W c)
    (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (neqFlag r a b) c c' k ∧ k ≤ 6 ∧
      c'.nreg r = (if c.nreg a = c.nreg b then 0 else 1) ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold neqFlag
  refine spec_seq (spec_instr (Exec.constN hc r 1 hW) fun hw₁ => ?_)
  by_cases h1 : c.nreg a < c.nreg b
  · refine spec_ifLtN_true (by ram_simp)
      (spec_skip hw₁ ?_)
    aesop
  · refine spec_ifLtN_false (by ram_simp) ?_
    by_cases h2 : c.nreg b < c.nreg a
    · refine spec_ifLtN_true (by ram_simp)
        (spec_skip hw₁ ?_)
      aesop
    · refine spec_ifLtN_false (by ram_simp)
        (spec_instr (Exec.constN hw₁ r 0 (Nat.zero_le _)) fun _ => ?_)
      aesop (add safe (by omega))

/-- Spec of `wrapZero`: cost `≤ 3`, `nreg r` is reset to `0` unless `nreg r < nreg m`. -/
theorem wrapZero_exec (r m : ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (wrapZero r m) c c' k ∧ k ≤ 3 ∧
      c'.nreg r = (if c.nreg r < c.nreg m then c.nreg r else 0) ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wrapZero
  by_cases h : c.nreg r < c.nreg m
  · refine spec_ifLtN_true h (spec_skip hc ?_)
    simp_all
  · refine spec_ifLtN_false h (spec_instr (Exec.constN hc r 0 (Nat.zero_le _)) fun _ => ?_)
    simp_all

end Kernels

/-! ### The loops over the tables -/

/-- One record of the trapezoid table (`ptr = nreg 208`): read `top`, `bot`; if they are not
adjacent, insert `(top, bot)`; advance. -/
def trapBody : Stmt :=
  .seq (block [.addN 218 208 224, .loadN 209 218, .addN 218 208 225, .loadN 210 218,
      .addN 220 209 205, .addN 221 210 205])
    (.seq (wrapZero 220 203) (.seq (wrapZero 221 203) (.seq (neqFlag 222 210 220)
      (.seq (neqFlag 227 209 221)
        (.seq (.ifLtN 204 222 (.ifLtN 204 227
            (.seq (block [.copyN 211 209, .copyN 212 210]) insStmt) .skip) .skip)
          (block [.addN 208 208 226, .addN 207 207 205]))))))

/-- One record of the vertex-chord table: insert `(src, dst)`; advance. -/
def chordBody : Stmt :=
  .seq (block [.loadN 211 208, .addN 218 208 224, .loadN 212 218])
    (.seq insStmt (block [.addN 208 208 225, .addN 207 207 205]))

/-- The state of the insertion: the pairs `L` inserted, and the constant registers. -/
def DState (DB HB SB n : ℕ) (L : List (ℕ × ℕ)) (c : Config) : Prop :=
  DRel c.nmem DB HB SB n (L.foldl ins []) ∧ c.nreg 206 = (L.foldl ins []).length ∧
    c.nreg 200 = DB ∧ c.nreg 201 = HB ∧ c.nreg 202 = SB ∧ c.nreg 203 = n ∧ c.nreg 204 = 0 ∧
    c.nreg 205 = 1 ∧ c.nreg 224 = 2 ∧ c.nreg 225 = 3 ∧ c.nreg 226 = 4

/-- The invariant of the loop over the trapezoid table. -/
def TrapInvD (P Q : Polygon) (T : TrapTable) (W DB HB SB M : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ T.length ∧ c.nreg 208 = c₀.nreg 9990 + 4 * c.nreg 207 ∧
    DState DB HB SB P.n (trapPairs Q (T.take (c.nreg 207))) c ∧
    (∀ r, (r < 206 ∨ 227 < r) → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < DB ∨ SB + M ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

section Loops

variable {P Q : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- One iteration of the loop over the trapezoid table. -/
theorem trapBody_inv (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} {c₀ : Config}
    (hTab : Core.TrapTableAt c₀.nmem (c₀.nreg 9990) T) (h9991 : c₀.nreg 9991 = T.length)
    (hTB : c₀.nreg 9990 + 4 * T.length ≤ DB) (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB)
    (hW : SB + M ≤ W) (hM : T.length + C.length ≤ M) (c : Config)
    (hI : TrapInvD P Q T W DB HB SB M c₀ c) (ht : c.nreg 207 < c.nreg 9991) :
    ∃ c' k, Exec P W trapBody c c' k ∧ TrapInvD P Q T W DB HB SB M c₀ c' ∧ k ≤ 200 ∧
      T.length - c'.nreg 207 < T.length - c.nreg 207 := by
  obtain ⟨hw, hj, hptr, ⟨hD, h206, h200, h201, h202, h203, h204, h205, h224, h225, h226⟩, hfn, hfr,
    hnm, hrm, hout⟩ := hI
  have e9991 : c.nreg 9991 = T.length := by simp_all
  rw [e9991] at ht
  set j := c.nreg 207 with hjdef
  set TB := c₀.nreg 9990 with hTBdef
  set r := T[j] with hr
  have hgetD : T.getD j ⟨0, 0, 0, 0⟩ = r := by
    grind
  obtain ⟨Dt, hDt⟩ := hT.exists_of_mem (List.getElem_mem ht)
  have htop : r.top < P.n := by rw [← hQn, hr, ← hDt]; exact Dt.top_lt hQ
  have hbot : r.bot < P.n := by rw [← hQn, hr, ← hDt]; exact Dt.bot_lt hQ
  have hrd := hTab j ht
  rw [hgetD] at hrd
  have m2 : c.nmem (TB + 4 * j + 2) = r.top := by grind
  have m3 : c.nmem (TB + 4 * j + 3) = r.bot := by grind
  set L := trapPairs Q (T.take j) with hL
  set E := L.foldl ins [] with hE
  have hELen : E.length ≤ j := (length_foldl_ins_le L []).trans (by
    simpa using length_trapPairs_take_le Q T j)
  have hW1 : 1 ≤ W := by omega
  unfold trapBody
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by grind
  have r1 : ∀ x, x ≠ 209 → x ≠ 210 → x ≠ 218 → x ≠ 220 → x ≠ 221 → c₁.nreg x = c.nreg x := by
    intro x a1 a2 a3 a4 a5; rw [hc₁]; config_simp; simp [a1, a2, a3, a4, a5]
  have e209 : c₁.nreg 209 = r.top := by
    rw [hc₁]; config_simp; ram_grind
  have e210 : c₁.nreg 210 = r.bot := by
    rw [hc₁]; config_simp; ram_grind
  have e220 : c₁.nreg 220 = r.top + 1 := by
    rw [hc₁]; config_simp; grind
  have e221 : c₁.nreg 221 = r.bot + 1 := by
    rw [hc₁]; config_simp; grind
  refine spec_seq (spec_use (wrapZero_exec (P := P) 220 203 c₁ hw₁) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨g220, gfn₂, gfr₂, gnm₂, grm₂, gout₂⟩
  refine spec_seq (spec_use (wrapZero_exec (P := P) 221 203 c₂ hw₂) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨g221, gfn₃, gfr₃, gnm₃, grm₃, gout₃⟩
  refine spec_seq (spec_use (neqFlag_exec (P := P) 222 210 220 (by decide) (by decide) c₃ hw₃ hW1)
    ?_)
  rintro c₄ k₄ hk₄ hw₄ ⟨g222, gfn₄, gfr₄, gnm₄, grm₄, gout₄⟩
  refine spec_seq (spec_use (neqFlag_exec (P := P) 227 209 221 (by decide) (by decide) c₄ hw₄ hW1)
    ?_)
  rintro c₅ k₅ hk₅ hw₅ ⟨g227, gfn₅, gfr₅, gnm₅, grm₅, gout₅⟩
  -- register bookkeeping through the kernels
  have R : ∀ x, x ≠ 220 → x ≠ 221 → x ≠ 222 → x ≠ 227 → c₅.nreg x = c₁.nreg x := by
    intro x a1 a2 a3 a4
    rw [gfn₅ x a4, gfn₄ x a3, gfn₃ x a2, gfn₂ x a1]
  have hmem₅ : c₅.nmem = c.nmem := by grind
  have hn₁ : c₁.nreg 203 = P.n := by grind
  have t1 : c₃.nreg 220 = (r.top + 1) % P.n := by
    rw [gfn₃ 220 (by decide), g220, e220, hn₁]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show r.top + 1 = P.n by omega, Nat.mod_self]
  have b1 : c₄.nreg 221 = (r.bot + 1) % P.n := by
    rw [gfn₄ 221 (by decide), g221, gfn₂ 221 (by decide), e221, gfn₂ 203 (by decide), hn₁]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show r.bot + 1 = P.n by omega, Nat.mod_self]
  have f1 : c₅.nreg 222 = (if r.bot = (r.top + 1) % P.n then 0 else 1) := by
    rw [gfn₅ 222 (by decide), g222, gfn₃ 210 (by decide), gfn₂ 210 (by decide), e210, t1]
  have f2 : c₅.nreg 227 = (if r.top = (r.bot + 1) % P.n then 0 else 1) := by
    rw [g227, gfn₄ 209 (by decide), gfn₃ 209 (by decide), gfn₂ 209 (by decide), e209, b1]
  have e204₅ : c₅.nreg 204 = 0 := by
    rw [R 204 (by decide) (by decide) (by decide) (by decide), r1 204 (by decide) (by decide)
      (by decide) (by decide) (by decide), h204]
  have hna : TrapRec.nonAdj Q.n r = true ↔ (0 < c₅.nreg 222 ∧ 0 < c₅.nreg 227) := by
    rw [f1, f2, TrapRec.nonAdj, decide_eq_true_iff, hQn]
    constructor
    · rintro ⟨h1, h2⟩; rw [ite_eq_right h1, ite_eq_right h2]; omega
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · grind
      grind
  -- the conditional insertion
  have hlenLt : E.length + 1 ≤ M := by omega
  have hcond : ∃ c₆ k₆, Exec P W (.ifLtN 204 222 (.ifLtN 204 227
      (.seq (block [.copyN 211 209, .copyN 212 210]) insStmt) .skip) .skip) c₅ c₆ k₆ ∧
      k₆ ≤ 170 ∧ DState DB HB SB P.n (trapPairs Q (T.take (j + 1))) c₆ ∧
      (∀ x, x ≠ 206 → (x < 211 ∨ 219 < x) → c₆.nreg x = c₅.nreg x) ∧ c₆.rreg = c₅.rreg ∧
      (∀ t, (t < DB ∨ SB + M ≤ t) → c₆.nmem t = c₅.nmem t) ∧ c₆.rmem = c₅.rmem ∧
      c₆.output = c₅.output := by
    have hstate : ∀ x, x = 200 ∨ x = 201 ∨ x = 202 ∨ x = 203 ∨ x = 204 ∨ x = 205 ∨ x = 206 ∨
        x = 224 ∨ x = 225 ∨ x = 226 → c₅.nreg x = c.nreg x := by
      intro x hx
      rw [R x (by omega) (by omega) (by omega) (by omega), r1 x (by omega) (by omega) (by omega)
        (by omega) (by omega)]
    have key : (trapPairs Q (T.take (j + 1))).foldl ins [] =
        if TrapRec.nonAdj Q.n r then ins E (r.top, r.bot) else E := by
      rw [trapPairs_take_succ Q ht, List.foldl_append, ← hr]
      split_ifs <;> rfl
    unfold DState
    rw [key]
    by_cases hnaj : TrapRec.nonAdj Q.n r = true
    · obtain ⟨p1, p2⟩ := hna.1 hnaj
      rw [ite_eq_left hnaj]
      refine spec_ifLtN_true (by rw [e204₅]; exact p1) (spec_ifLtN_true (by rw [e204₅]; exact p2) ?_)
      refine spec_seq ?_
      exec_block
      refine spec_use (insStmt_exec (P := P) (DB := DB) (HB := HB) (SB := SB) (n := P.n) (E := E)
        (a := r.top) (b := r.bot) _ ‹_›
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htop hbot ?_ (by omega) hl2 (by omega)) ?_
      · config_simp; rw [hstate 200 (by simp), h200]
      · config_simp; rw [hstate 201 (by simp), h201]
      · config_simp; rw [hstate 202 (by simp), h202]
      · config_simp; rw [hstate 204 (by simp), h204]
      · config_simp; rw [hstate 205 (by simp), h205]
      · config_simp; rw [hstate 206 (by simp), h206]
      · config_simp; rw [R 209 (by decide) (by decide) (by decide) (by decide), e209]
      · config_simp; rw [R 210 (by decide) (by decide) (by decide) (by decide), e210]
      · config_simp; rw [hmem₅]; exact hD
      rintro c₆ k₆ hk₆ hw₆ ⟨hD₆, h206₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
      have hcnt : E.countP (fun e => decide (e.1 = min r.top r.bot)) ≤ 10 :=
        countP_foldl_ins_le hQ hT hC (L := L)
          (fun e he => List.mem_append_left _ (trapPairs_sub Q T j e he)) (min r.top r.bot)
      refine ⟨by omega, ⟨hD₆, h206₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x h1 hx => ?_,
        by rw [hfr₆], fun t ht' => ?_, by rw [hrm₆], by rw [hout₆]⟩
      all_goals first
        | (rw [hfn₆ _ (by decide) (by omega)]; config_simp; rw [hstate _ (by simp)]; assumption)
        | skip
      · rw [hfn₆ x h1 (by omega)]; config_simp
        rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
      · rw [hnm₆ t (by omega)]
    · have hz : ¬ (0 < c₅.nreg 222 ∧ 0 < c₅.nreg 227) := fun h => hnaj (hna.2 h)
      rw [ite_eq_right hnaj]
      have hDs : DState DB HB SB P.n L c₅ := by
        refine ⟨by rw [hmem₅]; exact hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (rw [hstate _ (by simp)]; assumption)
      by_cases p1 : 0 < c₅.nreg 222
      · have p2 : ¬ 0 < c₅.nreg 227 := fun h => hz ⟨p1, h⟩
        refine spec_ifLtN_true (by rw [e204₅]; exact p1)
          (spec_ifLtN_false (by rw [e204₅]; exact p2) (spec_skip hw₅ ?_))
        exact ⟨by omega, hDs, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
      · refine spec_ifLtN_false (by rw [e204₅]; exact p1) (spec_skip hw₅ ?_)
        exact ⟨by omega, hDs, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
  refine spec_seq (spec_use hcond ?_)
  rintro c₆ k₆ hk₆ hw₆ ⟨hDs₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
  have e208 : c₆.nreg 208 = TB + 4 * j := by
    rw [hfn₆ 208 (by decide) (by omega), R 208 (by decide) (by decide) (by decide) (by decide),
      r1 208 (by decide) (by decide) (by decide) (by decide) (by decide), hptr]
  have e207 : c₆.nreg 207 = j := by
    rw [hfn₆ 207 (by decide) (by omega), R 207 (by decide) (by decide) (by decide) (by decide),
      r1 207 (by decide) (by decide) (by decide) (by decide) (by decide)]
  exec_block
  · rw [e208, hDs₆.2.2.2.2.2.2.2.2.2.2]; omega
  · config_simp; rw [e207, hDs₆.2.2.2.2.2.2.2.1]; omega
  refine ⟨⟨‹_›, ?_, ?_, ?_, fun x hx => ?_, ?_, fun t ht' => ?_, ?_, ?_⟩, by omega, ?_⟩
  · config_simp; rw [e207, hDs₆.2.2.2.2.2.2.2.1]; omega
  · config_simp; rw [e207, e208, hDs₆.2.2.2.2.2.2.2.1, hDs₆.2.2.2.2.2.2.2.2.2.2]; ring
  · config_simp
    rw [e207, hDs₆.2.2.2.2.2.2.2.1]
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hDs₆
    exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩
  · config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hfn₆ x (by omega) (by omega), R x (by omega) (by omega) (by omega) (by omega),
      r1 x (by omega) (by omega) (by omega) (by omega) (by omega), hfn x hx]
  · config_simp; rw [hfr₆, gfr₅, gfr₄, gfr₃, gfr₂, hc₁]; exact hfr
  · config_simp; rw [hnm₆ t ht', hmem₅, hnm t ht']
  · config_simp; rw [hrm₆, grm₅, grm₄, grm₃, grm₂, hc₁]; exact hrm
  · config_simp; rw [hout₆, gout₅, gout₄, gout₃, gout₂, hc₁]; exact hout
  · config_simp; rw [e207, hDs₆.2.2.2.2.2.2.2.1]; omega

/-- The invariant of the loop over the vertex-chord table. -/
def ChordInvD (P Q : Polygon) (T : TrapTable) (C : List ChordRec) (W DB HB SB M : ℕ)
    (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ C.length ∧ c.nreg 208 = c₀.nreg 9992 + 3 * c.nreg 207 ∧
    DState DB HB SB P.n (trapPairs Q T ++ chordPairs (C.take (c.nreg 207))) c ∧
    (∀ r, (r < 206 ∨ 227 < r) → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < DB ∨ SB + M ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the loop over the vertex-chord table. -/
theorem chordBody_inv (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} {c₀ : Config}
    (hCab : Core.ChordTableAt c₀.nmem (c₀.nreg 9992) C) (h9993 : c₀.nreg 9993 = C.length)
    (hCB : c₀.nreg 9992 + 3 * C.length ≤ DB) (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB)
    (hW : SB + M ≤ W) (hM : T.length + C.length ≤ M) (c : Config)
    (hI : ChordInvD P Q T C W DB HB SB M c₀ c) (ht : c.nreg 207 < c.nreg 9993) :
    ∃ c' k, Exec P W chordBody c c' k ∧ ChordInvD P Q T C W DB HB SB M c₀ c' ∧ k ≤ 172 ∧
      C.length - c'.nreg 207 < C.length - c.nreg 207 := by
  obtain ⟨hw, hj, hptr, ⟨hD, h206, h200, h201, h202, h203, h204, h205, h224, h225, h226⟩, hfn, hfr,
    hnm, hrm, hout⟩ := hI
  have e9993 : c.nreg 9993 = C.length := by simp_all
  rw [e9993] at ht
  set j := c.nreg 207 with hjdef
  set CB := c₀.nreg 9992 with hCBdef
  set r := C[j] with hr
  have hgetD : C.getD j ⟨0, false, 0⟩ = r := by
    grind
  have hval := (hC.1 r).1 (List.getElem_mem ht)
  have hsrc : r.src < P.n := by rw [← hQn]; exact hval.1
  have hdst : r.dst < P.n := by rw [← hQn]; exact hval.2.1
  have hrd := hCab j ht
  rw [hgetD] at hrd
  have m0 : c.nmem (CB + 3 * j) = r.src := by grind
  have m2 : c.nmem (CB + 3 * j + 2) = r.dst := by grind
  set L := trapPairs Q T ++ chordPairs (C.take j) with hL
  set E := L.foldl ins [] with hE
  have hELen : E.length ≤ T.length + j := (length_foldl_ins_le L []).trans (by
    simp only [hL, List.length_nil, Nat.zero_add, List.length_append]
    have := length_chordPairs_take_le C j
    grind [trapPairs, List.length_map])
  unfold chordBody
  refine spec_seq ?_
  exec_block
  · config_simp; omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by grind
  have r1 : ∀ x, x ≠ 211 → x ≠ 212 → x ≠ 218 → c₁.nreg x = c.nreg x := by
    intro x a1 a2 a3; rw [hc₁]; config_simp; simp [a1, a2, a3]
  have hcnt : E.countP (fun e => decide (e.1 = min r.src r.dst)) ≤ 10 :=
    countP_foldl_ins_le hQ hT hC (L := L) (fun e he => by
      rcases List.mem_append.1 he with h | h
      · grind
      · exact List.mem_append_right _ (chordPairs_sub C j e h)) (min r.src r.dst)
  refine spec_seq (spec_use (insStmt_exec (P := P) (DB := DB) (HB := HB) (SB := SB) (n := P.n)
    (E := E) (a := r.src) (b := r.dst) c₁ hw₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsrc hdst ?_ (by omega) hl2
    (by omega)) ?_)
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · rw [hc₁]; config_simp; ram_grind
  · rw [hc₁]; config_simp; ram_grind
  · grind
  rintro c₂ k₂ hk₂ hw₂ ⟨hD₂, h206₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have R : ∀ x, x ≠ 206 → (x < 211 ∨ 219 < x) → c₂.nreg x = c.nreg x := by
    intro x a1 a2
    rw [hfn₂ x a1 (by omega), r1 x (by omega) (by omega) (by omega)]
  have e208 : c₂.nreg 208 = CB + 3 * j := by grind
  have e207 : c₂.nreg 207 = j := R 207 (by decide) (by omega)
  have key : (trapPairs Q T ++ chordPairs (C.take (j + 1))).foldl ins [] = ins E (r.src, r.dst) := by
    rw [chordPairs_take_succ ht, ← List.append_assoc, List.foldl_append, ← hr]
    rfl
  exec_block
  · grind
  · config_simp; grind
  refine ⟨⟨‹_›, ?_, ?_, ?_, fun x hx => ?_, ?_, fun t ht' => ?_, ?_, ?_⟩, by omega, ?_⟩
  · config_simp; grind
  · config_simp
    grind
  · config_simp
    rw [e207, R 205 (by decide) (by omega), h205]
    unfold DState
    rw [key]
    refine ⟨hD₂, h206₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (config_simp; grind)
  · config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hfn₂ x (by omega) (by omega), r1 x (by omega) (by omega) (by omega), hfn x hx]
  · grind
  · config_simp; rw [hnm₂ t (by omega), hc₁]; ram_grind
  · grind
  · grind
  · config_simp; rw [e207, R 205 (by decide) (by omega), h205]; omega

end Loops

/-! ### The whole program -/

/-- Clear one head cell: `head[i] := 0; i := i + 1`. -/
def headBody : Stmt := block [.addN 218 201 207, .storeN 218 204, .addN 207 207 205]

/-- Clear the head array. -/
def headLoop : Stmt := .whileLtN 207 203 headBody

/-- `n`, the constants `0, 1, 2, 3, 4`, `ND := 0`, `i := 0`. -/
def diagInit : Stmt :=
  block [.inputSize 203, .constN 204 0, .constN 205 1, .constN 224 2, .constN 225 3,
    .constN 226 4, .constN 206 0, .constN 207 0]

/-- The loop over the trapezoid table. -/
def trapLoop : Stmt := .whileLtN 207 9991 trapBody

/-- The loop over the vertex-chord table. -/
def chordLoop : Stmt := .whileLtN 207 9993 chordBody

/-- **The diagonal-list program.** -/
def diagStmt : Stmt :=
  .seq diagInit (.seq headLoop (.seq (block [.constN 207 0, .copyN 208 9990])
    (.seq trapLoop (.seq (block [.constN 207 0, .copyN 208 9992]) chordLoop))))

section Whole

variable {P Q : Polygon} {W : ℕ}

/-- The invariant of the head-clearing loop. -/
def HeadInv (W HB n : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ n ∧ (∀ v < c.nreg 207, c.nmem (HB + v) = 0) ∧
    (∀ r, r ≠ 207 → r ≠ 218 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < HB ∨ HB + n ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the head-clearing loop. -/
theorem headBody_inv {HB n : ℕ} {c₀ : Config} (h201 : c₀.nreg 201 = HB) (h203 : c₀.nreg 203 = n)
    (h204 : c₀.nreg 204 = 0) (h205 : c₀.nreg 205 = 1) (hW : HB + n ≤ W) (c : Config)
    (hI : HeadInv W HB n c₀ c) (ht : c.nreg 207 < c.nreg 203) :
    ∃ c' k, Exec P W headBody c c' k ∧ HeadInv W HB n c₀ c' ∧ k ≤ 3 ∧
      n - c'.nreg 207 < n - c.nreg 207 := by
  obtain ⟨hw, hi, hz, hfn, hfr, hnm, hrm, hout⟩ := hI
  have e201 : c.nreg 201 = HB := by simp_all
  have e203 : c.nreg 203 = n := by simp_all
  have e204 : c.nreg 204 = 0 := by simp_all
  have e205 : c.nreg 205 = 1 := by simp_all
  rw [e203] at ht
  unfold headBody
  exec_block
  · rw [e201]; omega
  · config_simp; rw [e205]; omega
  refine ⟨⟨‹_›, ?_, fun v hv => ?_, fun r h1 h2 => ?_, hfr, fun t ht' => ?_, hrm, hout⟩,
    by omega, ?_⟩
  · simp_all
  · config_simp
    config_simp at hv
    rw [e205] at hv
    rw [e201, e204]
    simp only [Machine.upd_apply]
    grind
  · simp_all
  · config_simp
    rw [e201, Machine.upd_other _ _ _ (by omega)]
    exact hnm t ht'
  · config_simp; rw [e205]; omega

set_option maxHeartbeats 1000000 in
/-- **Spec of the diagonal-list program.**  From the two tables of `Q` in memory (below `DB`)
and the layout `DB + 2 M ≤ HB`, `HB + n ≤ SB`, `SB + M ≤ W` with `M ≥ |T| + |C|`, `diagStmt`
leaves in the band at `DB` a list `E` of `nreg 206 = |E|` pairs which is a permutation of
`diagList Q T C`, at cost `≤ 202 |T| + 174 |C| + 5 n + 20`.  It writes only the natural
registers `203 … 227` and the memory `[DB, SB + M)`. -/
theorem diagStmt_exec (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h9991 : c.nreg 9991 = T.length) (h9993 : c.nreg 9993 = C.length)
    (hTab : Core.TrapTableAt c.nmem (c.nreg 9990) T)
    (hCab : Core.ChordTableAt c.nmem (c.nreg 9992) C)
    (hTB : c.nreg 9990 + 4 * T.length ≤ DB) (hCB : c.nreg 9992 + 3 * C.length ≤ DB)
    (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB) (hW : SB + M ≤ W)
    (hM : T.length + C.length ≤ M) (h4 : 4 ≤ W) :
    ∃ c' k, Exec P W diagStmt c c' k ∧ k ≤ 202 * T.length + 174 * C.length + 5 * P.n + 20 ∧
      ∃ E : List (ℕ × ℕ), E.Perm (diagList Q T C) ∧ c'.nreg 206 = E.length ∧
        (∀ j < E.length, c'.nmem (DB + 2 * j) = (E.getD j (0, 0)).1 ∧
          c'.nmem (DB + 2 * j + 1) = (E.getD j (0, 0)).2) ∧
        (∀ r, (r < 203 ∨ 227 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        (∀ t, (t < DB ∨ SB + M ≤ t) → c'.nmem t = c.nmem t) ∧ c'.rmem = c.rmem ∧
        c'.output = c.output := by
  unfold diagStmt
  refine spec_seq ?_
  unfold diagInit
  exec_block
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by rw [hc₁]; assumption
  have r1 : ∀ x, (x < 203 ∨ (207 < x ∧ x < 224) ∨ 226 < x) → c₁.nreg x = c.nreg x := by
    intro x hx; rw [hc₁]; config_simp
    simp [show x ≠ 203 by omega, show x ≠ 204 by omega, show x ≠ 205 by omega,
      show x ≠ 206 by omega, show x ≠ 207 by omega, show x ≠ 224 by omega,
      show x ≠ 225 by omega, show x ≠ 226 by omega]
  have c203 : c₁.nreg 203 = P.n := by rw [hc₁]; config_simp
  have c204 : c₁.nreg 204 = 0 := by rw [hc₁]; config_simp
  have c205 : c₁.nreg 205 = 1 := by rw [hc₁]; config_simp
  have c206 : c₁.nreg 206 = 0 := by rw [hc₁]; config_simp
  have c207 : c₁.nreg 207 = 0 := by rw [hc₁]; config_simp
  have c224 : c₁.nreg 224 = 2 := by rw [hc₁]; config_simp
  have c225 : c₁.nreg 225 = 3 := by rw [hc₁]; config_simp
  have c226 : c₁.nreg 226 = 4 := by rw [hc₁]; config_simp
  have c201 : c₁.nreg 201 = HB := by simp_all
  -- clear the heads
  have hH₀ : HeadInv W HB P.n c₁ c₁ :=
    ⟨hw₁, by rw [c207]; omega, fun v hv => by rw [c207] at hv; omega, fun _ _ _ => rfl, rfl,
      fun _ _ => rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hle₂, hz₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (HeadInv W HB P.n c₁) (fun d => P.n - d.nreg 207) 3
      (fun _ h => h.1) (fun d hd ht => headBody_inv c201 c203 c204 c205 (by omega) d hd ht) hH₀
  unfold headLoop
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  have e207₂ : c₂.nreg 207 = P.n := by
    grind
  have R2 : ∀ x, x ≠ 207 → x ≠ 218 → c₂.nreg x = c₁.nreg x := hfn₂
  -- the memory relation for the empty list
  have hD₀ : DRel c₂.nmem DB HB SB P.n [] := by
    refine ⟨fun j hj => absurd hj (by simp), fun v hv => ?_⟩
    show c₂.nmem (HB + v) = 0
    grind
  have hmem₂ : ∀ t, (t < DB ∨ SB + M ≤ t) → c₂.nmem t = c.nmem t := by
    intro t ht
    rw [hnm₂ t (by omega), hc₁]
  -- the trapezoid loop
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_name fun c₃ hc₃ => ?_
  have hw₃ : WordsBounded W c₃ := by rw [hc₃]; assumption
  have R3 : ∀ x, x ≠ 207 → x ≠ 208 → c₃.nreg x = c₂.nreg x := by
    intro x a1 a2; rw [hc₃]; config_simp; simp [a1, a2]
  have g : ∀ x, (x < 203 ∨ 227 < x) → c₃.nreg x = c.nreg x := by
    intro x hx
    rw [R3 x (by omega) (by omega), R2 x (by omega) (by omega), r1 x (by omega)]
  have g' : ∀ x, x = 203 ∨ x = 204 ∨ x = 205 ∨ x = 206 ∨ x = 224 ∨ x = 225 ∨ x = 226 →
      c₃.nreg x = c₁.nreg x := by
    intro x hx
    rw [R3 x (by omega) (by omega), R2 x (by omega) (by omega)]
  have hTI : TrapInvD P Q T W DB HB SB M c₃ c₃ := by
    refine ⟨hw₃, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => rfl, rfl,
      fun _ _ => rfl, rfl, rfl⟩
    · rw [hc₃]; config_simp; omega
    · rw [hc₃]; config_simp; omega
    · have e : c₃.nreg 207 = 0 := by rw [hc₃]; config_simp
      rw [e, List.take_zero]
      show DRel c₃.nmem DB HB SB P.n []
      rw [hc₃]; exact hD₀
    · have e : c₃.nreg 207 = 0 := by rw [hc₃]; config_simp
      rw [e, List.take_zero, g' 206 (by simp), c206]; rfl
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    grind
  have hmem₃ : c₃.nmem = c₂.nmem := by rw [hc₃]
  have hTab₃ : Core.TrapTableAt c₃.nmem (c₃.nreg 9990) T := by
    rw [g 9990 (by omega)]
    intro i hi
    rw [hmem₃, hmem₂ _ (by omega), hmem₂ _ (by omega), hmem₂ _ (by omega), hmem₂ _ (by omega)]
    exact hTab i hi
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hj₄, hptr₄, hDs₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩, hexit₄, hk₄⟩ :=
    Exec.whileLtN_bounded (P := P) (TrapInvD P Q T W DB HB SB M c₃)
      (fun d => T.length - d.nreg 207) 200 (fun _ h => h.1)
      (fun d hd ht => trapBody_inv hQ hQn hT hC hTab₃ (by rw [g 9991 (by omega), h9991])
        (by rw [g 9990 (by omega)]; exact hTB) hl1 hl2 hW hM d hd ht) hTI
  unfold trapLoop
  refine spec_seq ⟨c₄, k₄, ex₄, ?_⟩
  have e207₄ : c₄.nreg 207 = T.length := by
    rw [hfn₄ 9991 (by omega), g 9991 (by omega), h9991] at hexit₄
    omega
  rw [e207₄, List.take_length] at hDs₄
  -- the chord loop
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_name fun c₅ hc₅ => ?_
  have hw₅ : WordsBounded W c₅ := by rw [hc₅]; assumption
  have R5 : ∀ x, x ≠ 207 → x ≠ 208 → c₅.nreg x = c₄.nreg x := by
    intro x a1 a2; rw [hc₅]; config_simp; simp [a1, a2]
  have g5 : ∀ x, (x < 203 ∨ 227 < x) → c₅.nreg x = c.nreg x := by
    intro x hx
    rw [R5 x (by omega) (by omega), hfn₄ x (by omega), g x hx]
  have hCI : ChordInvD P Q T C W DB HB SB M c₅ c₅ := by
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hDs₄
    refine ⟨hw₅, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => rfl, rfl,
      fun _ _ => rfl, rfl, rfl⟩
    · rw [hc₅]; config_simp; omega
    · rw [hc₅]; config_simp; omega
    · have e : c₅.nreg 207 = 0 := by rw [hc₅]; config_simp
      rw [e, List.take_zero]
      simp only [chordPairs, List.map_nil, List.append_nil]
      rw [hc₅]; exact d1
    · have e : c₅.nreg 207 = 0 := by rw [hc₅]; config_simp
      rw [e, List.take_zero]
      simp only [chordPairs, List.map_nil, List.append_nil]
      rw [R5 206 (by decide) (by decide)]; exact d2
    · rw [R5 200 (by decide) (by decide)]; exact d3
    · rw [R5 201 (by decide) (by decide)]; exact d4
    · rw [R5 202 (by decide) (by decide)]; exact d5
    · rw [R5 203 (by decide) (by decide)]; exact d6
    · rw [R5 204 (by decide) (by decide)]; exact d7
    · rw [R5 205 (by decide) (by decide)]; exact d8
    · rw [R5 224 (by decide) (by decide)]; exact d9
    · rw [R5 225 (by decide) (by decide)]; exact d10
    · rw [R5 226 (by decide) (by decide)]; exact d11
  have hmem₅ : ∀ t, (t < DB ∨ SB + M ≤ t) → c₅.nmem t = c.nmem t := by
    intro t ht
    have e : c₅.nmem = c₄.nmem := by rw [hc₅]
    rw [e, hnm₄ t ht, hmem₃, hmem₂ t ht]
  have hCab₅ : Core.ChordTableAt c₅.nmem (c₅.nreg 9992) C := by
    rw [g5 9992 (by omega)]
    intro i hi
    rw [hmem₅ _ (by omega), hmem₅ _ (by omega), hmem₅ _ (by omega)]
    exact hCab i hi
  obtain ⟨c₆, k₆, ex₆, ⟨hw₆, hj₆, hptr₆, hDs₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩, hexit₆, hk₆⟩ :=
    Exec.whileLtN_bounded (P := P) (ChordInvD P Q T C W DB HB SB M c₅)
      (fun d => C.length - d.nreg 207) 172 (fun _ h => h.1)
      (fun d hd ht => chordBody_inv hQ hQn hT hC hCab₅ (by rw [g5 9993 (by omega), h9993])
        (by rw [g5 9992 (by omega)]; exact hCB) hl1 hl2 hW hM d hd ht) hCI
  unfold chordLoop
  refine ⟨c₆, k₆, ex₆, ?_⟩
  have e207₆ : c₆.nreg 207 = C.length := by
    rw [hfn₆ 9993 (by omega), g5 9993 (by omega), h9993] at hexit₆
    omega
  rw [e207₆, List.take_length] at hDs₆
  obtain ⟨d1, d2, -⟩ := hDs₆
  have c5_207 : c₅.nreg 207 = 0 := by rw [hc₅]; config_simp
  have c3_207 : c₃.nreg 207 = 0 := by rw [hc₃]; config_simp
  rw [c5_207] at hk₆
  rw [c3_207] at hk₄
  rw [c207] at hk₂
  refine ⟨by simp only [Nat.sub_zero] at hk₂ hk₄ hk₆; nlinarith, _, foldl_ins_perm T C, d2, d1.band,
    fun x hx => ?_, ?_, fun t ht => ?_, ?_, ?_⟩
  · rw [hfn₆ x (by omega), g5 x (by omega)]
  · rw [hfr₆, hc₅]; config_simp; rw [hfr₄, hc₃]; config_simp; rw [hfr₂, hc₁]
  · have e : c₆.nmem t = c₅.nmem t := hnm₆ t ht
    rw [e, hmem₅ t ht]
  · rw [hrm₆, hc₅]; config_simp; rw [hrm₄, hc₃]; config_simp; rw [hrm₂, hc₁]
  · rw [hout₆, hc₅]; config_simp; rw [hout₄, hc₃]; config_simp; rw [hout₂, hc₁]

end Whole

end

end Chazelle.Final
