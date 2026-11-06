module

public import Chazelle.Core.SweepEvStopSort2
public import Chazelle.Core.SweepEvInit3

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 3 (the dedupe pass)

After the sort, the sorted indices `L` lie at `srSB`.  The pass `ssDedup` walks `L`: the first
index is written; every later index is written iff its key differs from that of the previous one
(the comparator `ssCmp` on `(x, prev)` answers `KLe (key x) (key prev)`, i.e. equality of the keys
since `L` is sorted).  The invariant is `DInv` (`SweepEvStopL.lean`) plus the written records
(`SsDI`); main lemma `ssDedup_exec`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR

@[expose] public section

/-! ## Lists -/

theorem ss_getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default]; simp; omega

theorem KLe.antisymm' {a b : ℝ × ℕ} (h1 : KLe a b) (h2 : KLe b a) : a = b := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · rw [h2] at h1; exact absurd h1 (lt_irrefl _)
  · rw [h1] at h2; exact absurd h2 (lt_irrefl _)
  · exact Prod.ext h1 (le_antisymm h1' h2')

/-! ## The program of the pass -/

/-- Check the record of `srX` against the previous one (`srP`); write it unless the keys agree. -/
def ssChk : Stmt :=
  .seq (block [.copyN 30000 srX, .copyN 30001 srP]) (.seq ssCmp (.ifLtN K0 30002 .skip ssWr))

/-- One step of the pass. -/
def ssBody : Stmt :=
  .seq (block [.addN srA srSB srJ, .loadN srX srA])
    (.seq (.ifLtN K0 srJ ssChk ssWr) (block [.copyN srP srX, .addN srJ srJ K1]))

/-- **The dedupe pass.** -/
def ssDedup : Stmt := .whileLtN srJ gRC ssBody

/-! ## Records -/

theorem stopRecs_snoc {m m' : ℕ → ℕ} {A : ℕ} {O : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : StopRecsAt m A O)
    (hk : ∀ a, A ≤ a → a < A + 5 * O.length → m' a = m a)
    (hn : m' (A + 5 * O.length) = x.1 ∧ m' (A + 5 * O.length + 1) = x.2.1 ∧
      m' (A + 5 * O.length + 2) = x.2.2.1 ∧ m' (A + 5 * O.length + 3) = x.2.2.2.1 ∧
      m' (A + 5 * O.length + 4) = x.2.2.2.2) : StopRecsAt m' A (O ++ [x]) := by
  intro i hi
  rw [ss_getD_snoc]
  simp only [List.length_append, List.length_singleton] at hi
  split_ifs with h1 h2
  · obtain ⟨a0, a1, a2, a3, a4⟩ := h i h1
    exact ⟨(hk _ (by omega) (by omega)).trans a0, (hk _ (by omega) (by omega)).trans a1,
      (hk _ (by omega) (by omega)).trans a2, (hk _ (by omega) (by omega)).trans a3,
      (hk _ (by omega) (by omega)).trans a4⟩
  · subst h2; exact hn
  · omega

theorem auxRecs_snoc {m m' : ℕ → ℕ} {A : ℕ} {O : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : AuxRecsAt m A O)
    (hk : ∀ a, A ≤ a → a < A + 5 * O.length → m' a = m a)
    (hn : m' (A + 5 * O.length) = x.1 ∧ m' (A + 5 * O.length + 1) = x.2.1 ∧
      m' (A + 5 * O.length + 2) = x.2.2.1 ∧ m' (A + 5 * O.length + 3) = x.2.2.2.1 ∧
      m' (A + 5 * O.length + 4) = x.2.2.2.2) : AuxRecsAt m' A (O ++ [x]) := by
  intro i hi
  rw [ss_getD_snoc]
  simp only [List.length_append, List.length_singleton] at hi
  split_ifs with h1 h2
  · obtain ⟨a0, a1, a2, a3, a4⟩ := h i h1
    exact ⟨(hk _ (by omega) (by omega)).trans a0, (hk _ (by omega) (by omega)).trans a1,
      (hk _ (by omega) (by omega)).trans a2, (hk _ (by omega) (by omega)).trans a3,
      (hk _ (by omega) (by omega)).trans a4⟩
  · subst h2; exact hn
  · omega

/-! ## The invariant of the pass -/

/-- **The state of the pass after `j` indices** of `L` (from the entry configuration `d₀`). -/
structure SsDI (P : Polygon) (W : ℕ) (J : Merge.Junction) (d2 RB S A₀ : ℕ) (m₀ : ℕ → ℕ)
    (L : List ℕ) (SBv B1 : ℕ) (d₀ : Config) (j : ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  qj : d.nreg srJ = j
  ctx : SsCtx J d2 RB S A₀ m₀ d
  sb : d.nreg srSB = SBv
  b1 : d.nreg sB = B1
  b2 : d.nreg aB = B1 + 5 * S
  mem : ∀ a, a < B1 → d.nmem a = d₀.nmem a
  recs : ∃ O, DInv (ssKey P J m₀ RB) L j O ∧ d.nreg sC = O.length ∧ O.length ≤ j ∧
    (0 < j → ∃ x', L[j - 1]? = some x' ∧ d.nreg srP = x') ∧
    StopRecsAt d.nmem B1 (O.map (rawRec m₀ RB)) ∧ AuxRecsAt d.nmem (B1 + 5 * S) (O.map (rawAux m₀ RB))
  regs : ∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → r ≠ sC →
    d.nreg r = d₀.nreg r
  rr : ∀ r, bandOf r ∉ oracleBands → d.rreg r = d₀.rreg r
  rm : d.rmem = d₀.rmem
  out : d.output = d₀.output

set_option maxRecDepth 20000 in
/-- **Writing a record keeps the invariant** (the item `x = L[j]` with a new key). -/
theorem ssWr_step {P : Polygon} {W : ℕ} {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {B1 : ℕ} {d₀ d : Config} {O : List ℕ} {x : ℕ}
    (hw : WordsBounded W d) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (hctx : SsCtx J d2 RB S A₀ m₀ d) (hb1 : d.nreg sB = B1) (hb2 : d.nreg aB = B1 + 5 * S)
    (_hmem : ∀ a, a < B1 → d.nmem a = d₀.nmem a) (hx : d.nreg srX = x) (hxS : x < S)
    (hC : d.nreg sC = O.length) (hO : O.length < S)
    (hst : StopRecsAt d.nmem B1 (O.map (rawRec m₀ RB)))
    (hax : AuxRecsAt d.nmem (B1 + 5 * S) (O.map (rawAux m₀ RB))) :
    ∃ d' k, Exec P W ssWr d d' k ∧ k = 53 ∧ d'.nreg sC = (O ++ [x]).length ∧
      StopRecsAt d'.nmem B1 ((O ++ [x]).map (rawRec m₀ RB)) ∧
      AuxRecsAt d'.nmem (B1 + 5 * S) ((O ++ [x]).map (rawAux m₀ RB)) ∧
      (∀ a, a < B1 → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV → r ≠ sC →
        d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨-, -, hRB, -, -, hK1, -, hm⟩ := hctx
  obtain ⟨d', k, ex, hk, hmem', hsC, hr, hrr, hrm, ho⟩ := ssWr_exec (P := P) hw hK1
    (by rw [hRB, hx, hb1, hC]; omega) (by rw [hb1, hb2, hC]; omega)
    (by rw [hb2, hC]; omega)
  rw [hRB, hx, hb1, hb2, hC] at hmem'
  have src : ∀ u, u < 11 → d.nmem (RB + 11 * x + u) = m₀ (RB + 11 * x + u) := fun u hu =>
    hm _ (by have : 11 * x + 11 ≤ 11 * S := by omega
             omega)
  have wD : ∀ t, t < 5 → d'.nmem (B1 + 5 * O.length + t) = m₀ (RB + 11 * x + ssOff t) :=
    fun t ht => by
      rw [hmem']; unfold ssWM
      rw [ite_eq_left (by omega), show B1 + 5 * O.length + t - (B1 + 5 * O.length) = t by omega]
      exact src _ (by unfold ssOff; split_ifs <;> omega)
  have wE : ∀ t, t < 5 → d'.nmem (B1 + 5 * S + 5 * O.length + t) = m₀ (RB + 11 * x + 6 + t) :=
    fun t ht => by
      rw [hmem']; unfold ssWM
      rw [ite_eq_right (by omega), ite_eq_left (by omega),
        show B1 + 5 * S + 5 * O.length + t - (B1 + 5 * S + 5 * O.length) = t by omega, show RB + 11 * x + 6 + t = RB + 11 * x + (6 + t) by omega]
      exact src _ (by omega)
  have kD : ∀ a, a < B1 + 5 * O.length → d'.nmem a = d.nmem a := fun a ha => by
    rw [hmem']; unfold ssWM; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have kE : ∀ a, a < B1 + 5 * S + 5 * O.length → (a < B1 + 5 * O.length ∨
      B1 + 5 * O.length + 5 ≤ a) → d'.nmem a = d.nmem a := fun a ha ha' => by
    rw [hmem']; unfold ssWM; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨d', k, ex, hk, by rw [hsC, hC]; simp, ?_, ?_, fun a ha => kD a (by omega),
    hr, hrr, hrm, ho⟩
  · rw [List.map_append, List.map_singleton]
    refine stopRecs_snoc hst (fun a _ ha => kD a (by simpa using ha)) ?_
    simp only [List.length_map, rawRec]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := wD 0 (by norm_num); simp only [ssOff] at this; simpa using this
    · have := wD 1 (by norm_num); simp only [ssOff] at this; simpa using this
    · have := wD 2 (by norm_num); simp only [ssOff] at this; simpa using this
    · have := wD 3 (by norm_num); simp only [ssOff] at this; simpa using this
    · have := wD 4 (by norm_num); simp only [ssOff] at this; simpa using this
  · rw [List.map_append, List.map_singleton]
    refine auxRecs_snoc hax (fun a ha0 ha => kE a (by simpa using ha) (by
      simp only [List.length_map] at ha; omega)) ?_
    simp only [List.length_map, rawAux]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := wE 0 (by norm_num); simpa using this
    · have := wE 1 (by norm_num); simpa using this
    · have := wE 2 (by norm_num); simpa using this
    · have := wE 3 (by norm_num); simpa using this
    · have := wE 4 (by norm_num); simpa using this

/-! ## One step of the pass -/

theorem ssCtx_keep {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ} {d d' : Config}
    (h : SsCtx J d2 RB S A₀ m₀ d)
    (hr : ∀ r, 240000 ≤ r → r < 250000 → (r < sw 3003 ∨ sw 3016 < r) → r ≠ sC →
      d'.nreg r = d.nreg r)
    (hm : ∀ a, a < A₀ → d'.nmem a = d.nmem a) : SsCtx J d2 RB S A₀ m₀ d' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have k : ∀ i, (i < 3003 ∨ (3016 < i ∧ i < 10000)) ∧ i ≠ 2601 →
      d'.nreg (sw i) = d.nreg (sw i) :=
    fun i hi => hr (sw i) (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega)
      (by unfold sC sw; omega)
  exact ⟨(k 2 (by norm_num)).trans h1, (k 659 (by norm_num)).trans h2,
    (k 4000 (by norm_num)).trans h3, (k 4001 (by norm_num)).trans h4,
    (k 610 (by norm_num)).trans h5, (k 611 (by norm_num)).trans h6,
    (k 3000 (by norm_num)).trans h7, fun a ha => (hm a ha).trans (h8 a ha)⟩

theorem ssBc_sub {r : ℕ} (h : bandOf r ∉ oracleBands) : bandOf r ∉ ssBc := fun h' =>
  h (by
    simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h' <;> rw [h'] <;> decide)

/-- The read of the next index. -/
def ssRd : List Instr := [.addN srA srSB srJ, .loadN srX srA]

/-- The advance. -/
def ssAdv : List Instr := [.copyN srP srX, .addN srJ srJ K1]

set_option maxRecDepth 20000 in
theorem ssRd_val (m f : ℕ → ℕ) : regB m ssRd f srX = m (f srSB + f srJ) ∧
    ∀ r, r ≠ srA → r ≠ srX → regB m ssRd f r = f r := by
  refine ⟨?_, fun r h1 h2 => ?_⟩
  · simp only [ssRd, regB, regI, srA, srX, srSB, srJ, sw, Nat.reduceAdd, upd_same]
  · simp only [ssRd, regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]

set_option maxRecDepth 20000 in
theorem ssAdv_val (m f : ℕ → ℕ) : regB m ssAdv f srP = f srX ∧ regB m ssAdv f srJ = f srJ + f K1 ∧
    ∀ r, r ≠ srP → r ≠ srJ → regB m ssAdv f r = f r := by
  refine ⟨?_, ?_, fun r h1 h2 => ?_⟩
  · simp only [ssAdv, regB, regI, srP, srX, srJ, K1, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other,
      Nat.reduceEqDiff, not_false_eq_true]
  · simp only [ssAdv, regB, regI, srP, srX, srJ, K1, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other,
      Nat.reduceEqDiff, not_false_eq_true]
  · simp only [ssAdv, regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]

set_option maxRecDepth 20000 in
theorem ssCp_val (m f : ℕ → ℕ) :
    regB m [.copyN 30000 srX, .copyN 30001 srP] f 30000 = f srX ∧
    regB m [.copyN 30000 srX, .copyN 30001 srP] f 30001 = f srP ∧
    ∀ r, r ≠ 30000 → r ≠ 30001 → regB m [.copyN 30000 srX, .copyN 30001 srP] f r = f r := by
  refine ⟨?_, ?_, fun r h1 h2 => ?_⟩
  · simp only [regB, regI, srP, srX, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other,
      Nat.reduceEqDiff, not_false_eq_true]
  · simp only [regB, regI, srP, srX, sw, Nat.reduceAdd, upd_same]
    rw [upd_other _ _ _ (by norm_num)]
  · simp only [regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]

end

end SweepEv

end Chazelle.Core
