module

public import Chazelle.Core.FuseAsmDedup
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
set_option maxHeartbeats 8000000

/-!
# WP-F fusion assembly, part 7: the deduplicating scan

`dsLoop` scans the sorted items at `B'` (`K` of them, each an index of a stored triple at `T`) and
appends the triple of item `j` at the allocator iff `j = 0` or it differs from the triple of item
`j - 1` (`ddp`).  Registers (band `bFuse`): `70220` index, `70221` cursor, `70222` item,
`70223` previous item, `70224 … 70226` its triple, `70227` scratch, `70228` flag, `70229`
address, `70230` bound `K`; constants `70105 = 1`, `70108 = 0`, base `70216 = T`.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The program -/

/-- Raise the flag if the two registers differ. -/
def neqS (a b : ℕ) : Stmt :=
  .seq (.ifLtN a b (.instr (.constN 70228 1)) .skip) (.ifLtN b a (.instr (.constN 70228 1)) .skip)

/-- Load the item and its triple; clear the flag. -/
def dsLoad : Stmt := block [.loadN 70222 70221, .addN 70229 70222 70222,
  .addN 70229 70229 70222, .addN 70229 70229 70216, .loadN 70224 70229,
  .addN 70229 70229 70105, .loadN 70225 70229, .addN 70229 70229 70105, .loadN 70226 70229,
  .constN 70228 0]

/-- Compare with the triple of the previous item. -/
def dsPrev : Stmt :=
  .seq (block [.addN 70229 70223 70223, .addN 70229 70229 70223, .addN 70229 70229 70216,
      .loadN 70227 70229])
    (.seq (neqS 70224 70227) (.seq (block [.addN 70229 70229 70105, .loadN 70227 70229])
      (.seq (neqS 70225 70227) (.seq (block [.addN 70229 70229 70105, .loadN 70227 70229])
        (neqS 70226 70227)))))

/-- The flag: the first item, or a new triple. -/
def dsFlag : Stmt := .ifLtN 70220 70105 (.instr (.constN 70228 1)) dsPrev

/-- Append the triple. -/
def dsCopy : Stmt := block [.storeN ALLOC 70224, .addN ALLOC ALLOC 70105, .storeN ALLOC 70225,
  .addN ALLOC ALLOC 70105, .storeN ALLOC 70226, .addN ALLOC ALLOC 70105,
  .addN 70219 70219 70105]

/-- One item. -/
def dsBody : Stmt :=
  .seq dsLoad (.seq dsFlag (.seq (.ifLtN 70108 70228 dsCopy .skip)
    (block [.copyN 70223 70222, .addN 70221 70221 70105, .addN 70220 70220 70105])))

/-- The scan. -/
def dsLoop : Stmt := .whileLtN 70220 70230 dsBody

/-! ## Pieces -/

theorem neqS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (a b : ℕ) (ha : a ≠ 70228) (hb : b ≠ 70228) :
    ∃ c' k, Exec P W (neqS a b) c c' k ∧ k ≤ 6 ∧
      c'.nreg 70228 = (if c.nreg a ≠ c.nreg b then 1 else c.nreg 70228) ∧
      (∀ r, r ≠ 70228 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have step : ∀ (x y : ℕ) (c : Config), WordsBounded W c → x ≠ 70228 → y ≠ 70228 →
      ∃ c' k, Exec P W (.ifLtN x y (.instr (.constN 70228 1)) .skip) c c' k ∧ k ≤ 3 ∧
        c'.nreg 70228 = (if c.nreg x < c.nreg y then 1 else c.nreg 70228) ∧
        (∀ r, r ≠ 70228 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := fun x y c hw _ _ => by
    by_cases h : c.nreg x < c.nreg y
    · have e := Exec.constN (P := P) hw 70228 1 hW
      exact ⟨_, _, .ifLtN_true h e, by omega, by simp [h], fun r hr => by simp [hr], rfl, rfl,
        rfl, rfl⟩
    · exact ⟨c, _, .ifLtN_false h (.skip hw), by omega, by simp [h], fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, m₁, rr₁, rm₁, o₁⟩ := step a b c hw ha hb
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := step b a c₁ e₁.wb_right hb ha
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, fun r hr => by rw [r₂ r hr, r₁ r hr],
    by rw [m₂, m₁], by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [v₂, v₁, r₁ a ha, r₁ b hb]
  by_cases h1 : c.nreg a < c.nreg b
  · simp [h1, show c.nreg a ≠ c.nreg b by omega]
  · by_cases h2 : c.nreg b < c.nreg a
    · simp [h2, show c.nreg a ≠ c.nreg b by omega]
    · simp [show c.nreg a = c.nreg b by omega]

theorem dsLoad_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {T x : ℕ}
    (hT : c.nreg 70216 = T) (h05 : c.nreg 70105 = 1) (hx : c.nmem (c.nreg 70221) = x)
    (hxW : T + 3 * x + 2 ≤ W) :
    ∃ c' k, Exec P W dsLoad c c' k ∧ k = 10 ∧ c'.nreg 70222 = x ∧
      c'.nreg 70224 = c.nmem (T + 3 * x) ∧ c'.nreg 70225 = c.nmem (T + 3 * x + 1) ∧
      c'.nreg 70226 = c.nmem (T + 3 * x + 2) ∧ c'.nreg 70228 = 0 ∧
      (∀ r, r ≠ 70222 → r ≠ 70224 → r ≠ 70225 → r ≠ 70226 → r ≠ 70228 → r ≠ 70229 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dsLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, hx, h05]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, hx, h05]
  all_goals first | rfl | (congr 1; ring)

theorem dsPrev_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {T p : ℕ} (hT : c.nreg 70216 = T) (h05 : c.nreg 70105 = 1) (hp : c.nreg 70223 = p)
    (hpW : T + 3 * p + 2 ≤ W) (h28 : c.nreg 70228 = 0) :
    ∃ c' k, Exec P W dsPrev c c' k ∧ k ≤ 30 ∧
      c'.nreg 70228 = (if (c.nreg 70224, c.nreg 70225, c.nreg 70226) ≠
        (c.nmem (T + 3 * p), c.nmem (T + 3 * p + 1), c.nmem (T + 3 * p + 2)) then 1 else 0) ∧
      (∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- first component
  obtain ⟨c₁, k₁, e₁, hk₁, v27, v29, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 70229 70223 70223, .addN 70229 70229 70223, .addN 70229 70229 70216,
        .loadN 70227 70229]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 70227 = c.nmem (T + 3 * p) ∧
      c₁.nreg 70229 = T + 3 * p ∧ (∀ r, r ≠ 70227 → r ≠ 70229 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hp]; omega)
    refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hp]
    all_goals first | rfl | ring
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, r₂, m₂, rr₂, rm₂, o₂⟩ :=
    neqS_exec (P := P) c₁ e₁.wb_right hW 70224 70227 (by decide) (by decide)
  -- second component
  have load : ∀ (d : Config) (v : ℕ), WordsBounded W d → d.nreg 70229 = v → d.nreg 70105 = 1 →
      v + 1 ≤ W → ∃ d' k, Exec P W (block [.addN 70229 70229 70105, .loadN 70227 70229]) d d' k ∧
        k = 2 ∧ d'.nreg 70227 = d.nmem (v + 1) ∧ d'.nreg 70229 = v + 1 ∧
        (∀ r, r ≠ 70227 → r ≠ 70229 → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧
        d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
    intro d v hwd hv h1 hvW
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hv, h1]; omega)
    refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hv, h1]
  have g2 : ∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₂.nreg r = c.nreg r := fun r a b d => by
    rw [r₂ r b, r₁ r a d]
  obtain ⟨c₃, k₃, e₃, hk₃, u27, u29, r₃, m₃, rr₃, rm₃, o₃⟩ := load c₂ (T + 3 * p) e₂.wb_right
    (by rw [r₂ _ (by decide), v29]) (by rw [g2 _ (by decide) (by decide) (by decide), h05])
    (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, r₄, m₄, rr₄, rm₄, o₄⟩ :=
    neqS_exec (P := P) c₃ e₃.wb_right hW 70225 70227 (by decide) (by decide)
  have g4 : ∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₄.nreg r = c.nreg r := fun r a b d => by
    rw [r₄ r b, r₃ r a d, g2 r a b d]
  obtain ⟨c₅, k₅, e₅, hk₅, w27, w29, r₅, m₅, rr₅, rm₅, o₅⟩ := load c₄ (T + 3 * p + 1)
    e₄.wb_right (by rw [r₄ _ (by decide), u29]) (by rw [g4 _ (by decide) (by decide) (by decide),
      h05]) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, r₆, m₆, rr₆, rm₆, o₆⟩ :=
    neqS_exec (P := P) c₅ e₅.wb_right hW 70226 70227 (by decide) (by decide)
  have ex : Exec P W dsPrev c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  refine ⟨c₆, _, ex, by omega, ?_, fun r a b d => by rw [r₆ r b, r₅ r a d, g4 r a b d], ?_, ?_,
    ?_, ?_⟩
  · have mm : ∀ x, c₅.nmem x = c.nmem x := fun x => by rw [m₅, m₄, m₃, m₂, m₁]
    have A2 : c₂.nreg 70228 = if c.nreg 70224 ≠ c.nmem (T + 3 * p) then 1 else 0 := by
      rw [f₂, r₁ _ (by decide) (by decide), v27, h28.symm.trans (r₁ _ (by decide) (by decide)).symm]
    have A4 : c₄.nreg 70228 = if c.nreg 70225 ≠ c.nmem (T + 3 * p + 1) then 1
        else c₂.nreg 70228 := by
      rw [f₄, r₃ _ (by decide) (by decide), u27, g2 _ (by decide) (by decide) (by decide),
        r₃ _ (by decide) (by decide), m₂, m₁]
    have A6 : c₆.nreg 70228 = if c.nreg 70226 ≠ c.nmem (T + 3 * p + 2) then 1
        else c₄.nreg 70228 := by
      rw [f₆, r₅ _ (by decide) (by decide), w27, g4 _ (by decide) (by decide) (by decide),
        r₅ _ (by decide) (by decide), m₄, m₃, m₂, m₁]
    rw [A6, A4, A2]
    simp only [ne_eq, Prod.mk.injEq, not_and_or]
    split_ifs <;> tauto
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁]

theorem dsCopy_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {a : ℕ}
    (hA : c.nreg ALLOC = a) (h05 : c.nreg 70105 = 1) (ha : a + 3 ≤ W) {n : ℕ}
    (h19 : c.nreg 70219 = n) (hn : n + 1 ≤ W) :
    ∃ c' k, Exec P W dsCopy c c' k ∧ k = 7 ∧ c'.nreg ALLOC = a + 3 ∧
      (∀ x, (x < a ∨ a + 3 ≤ x) → c'.nmem x = c.nmem x) ∧
      c'.nmem a = c.nreg 70224 ∧ c'.nmem (a + 1) = c.nreg 70225 ∧ c'.nmem (a + 2) = c.nreg 70226 ∧
      c'.nreg 70219 = n + 1 ∧ (∀ r, r ≠ ALLOC → r ≠ 70219 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dsCopy
  have hA' : c.nreg 9999 = a := hA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h05, h19, ALLOC]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h05, h19, ALLOC])
  · have a1' : r ≠ 9999 := a1
    simp (disch := omega) only [Machine.upd_other]

/-! ## The loop -/

/-- The triples of the sorted items. -/
def stl (m₀ : ℕ → ℕ) (T B K : ℕ) : List (ℕ × ℕ × ℕ) := (SortL.seg m₀ B K).map (trip m₀ T)

theorem stl_getD {m₀ : ℕ → ℕ} {T B K j : ℕ} (hj : j < K) :
    (stl m₀ T B K).getD j (0, 0, 0) = trip m₀ T (m₀ (B + j)) := by
  simp [stl, SortL.seg, List.getD_eq_getElem?_getD, hj]

/-- The invariant of the scan. -/
structure DSI (W K T B LB : ℕ) (m₀ : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  j_le : c.nreg 70220 ≤ K
  cur : c.nreg 70221 = B + c.nreg 70220
  prev : 0 < c.nreg 70220 → c.nreg 70223 = m₀ (B + (c.nreg 70220 - 1))
  alloc : c.nreg ALLOC = LB + 3 * (ddp (stl m₀ T B K) (0, 0, 0) (c.nreg 70220)).length
  list : ChordListAt c.nmem LB (ddp (stl m₀ T B K) (0, 0, 0) (c.nreg 70220))
  cnt : c.nreg 70219 = (ddp (stl m₀ T B K) (0, 0, 0) (c.nreg 70220)).length
  low : ∀ a, a < LB → c.nmem a = m₀ a
  regs : ∀ r, (r < 70219 ∨ 70229 < r) → r ≠ ALLOC → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

theorem ddp_length_le {α : Type*} [DecidableEq α] (l : List α) (d : α) (n : ℕ) :
    (ddp l d n).length ≤ n := by
  unfold ddp; rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem dsBody_step {P : Polygon} {W K T B LB : ℕ} {m₀ : ℕ → ℕ} {c₀ c : Config}
    (hI : DSI W K T B LB m₀ c₀ c) (ht : c.nreg 70220 < K) (h05 : c₀.nreg 70105 = 1)
    (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70216 = T)
    (hitems : ∀ j, j < K → m₀ (B + j) < K) (hTB : T + 3 * K ≤ LB) (hBL : B + K ≤ LB)
    (hW : LB + 3 * K + 3 ≤ W) :
    ∃ c' k, Exec P W dsBody c c' k ∧ DSI W K T B LB m₀ c₀ c' ∧ k ≤ 58 ∧ 3 ≤ k ∧
      c'.nreg 70220 = c.nreg 70220 + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, c.nreg 70220 = j := ⟨_, rfl⟩
  rw [hj] at ht
  have hreg := hI.regs
  have r05 : c.nreg 70105 = 1 := by rw [hreg _ (by norm_num) (by decide), h05]
  have r08 : c.nreg 70108 = 0 := by rw [hreg _ (by norm_num) (by decide), h08]
  have r16 : c.nreg 70216 = T := by rw [hreg _ (by norm_num) (by decide), h16]
  obtain ⟨x, hx⟩ : ∃ x, m₀ (B + j) = x := ⟨_, rfl⟩
  have hxK : x < K := hx ▸ hitems j ht
  have hW1 : 1 ≤ W := by omega
  -- load
  obtain ⟨c₁, k₁, e₁, hk₁, v22, v24, v25, v26, v28, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dsLoad_exec (P := P) c hI.wb r16 r05 (x := x)
      (by rw [hI.cur, hj, hI.low _ (by omega), hx]) (by omega)
  have mT : ∀ k, k < 3 → c.nmem (T + 3 * x + k) = m₀ (T + 3 * x + k) := fun k hk =>
    hI.low _ (by omega)
  have mT0 : c.nmem (T + 3 * x) = m₀ (T + 3 * x) := by simpa using mT 0 (by omega)
  -- flag
  have hkeep : keep (stl m₀ T B K) (0, 0, 0) j = true ↔
      (j = 0 ∨ trip m₀ T x ≠ trip m₀ T (m₀ (B + (j - 1)))) := by
    unfold keep
    rw [stl_getD ht, hx]
    by_cases h0 : j = 0
    · simp [h0]
    · rw [stl_getD (by omega)]; simp [h0]
  obtain ⟨c₂, k₂, e₂, hk₂, v2, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W dsFlag c₁ c₂ k₂ ∧
      k₂ ≤ 32 ∧ (c₂.nreg 70228 = if keep (stl m₀ T B K) (0, 0, 0) j then 1 else 0) ∧
      (∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q20 : c₁.nreg 70220 = j := by
      rw [r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hj]
    have q05 : c₁.nreg 70105 = 1 := by
      rw [r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r05]
    unfold dsFlag
    by_cases h0 : j = 0
    · have e := Exec.constN (P := P) e₁.wb_right 70228 1 hW1
      refine ⟨_, _, .ifLtN_true (by rwo [q20, q05]) e, by omega, ?_, fun r _ hr _ => by
        simp [hr], rfl, rfl, rfl, rfl⟩
      simp only [upd_same]
      rw [ite_eq_left ((hkeep).2 (Or.inl h0))]
    · have hp : c₁.nreg 70223 = m₀ (B + (j - 1)) := by
        rw [r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [← hj]; exact hI.prev (by omega)
      have hpK : m₀ (B + (j - 1)) < K := hitems _ (by omega)
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dsPrev_exec (P := P) (T := T)
        (p := m₀ (B + (j - 1))) c₁ e₁.wb_right hW1
        ((r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r16)
        q05 hp (by omega) v28
      refine ⟨c₂, _, .ifLtN_false (by rwo [q20, q05]) e₂, by omega, ?_,
        fun r a b d => r₂ r a b d, m₂, rr₂, rm₂, o₂⟩
      rw [f₂, v24, v25, v26, m₁, mT0, mT 1 (by omega), mT 2 (by omega),
        hI.low _ (by omega), hI.low _ (by omega), hI.low _ (by omega)]
      by_cases hk : keep (stl m₀ T B K) (0, 0, 0) j = true
      · have := (hkeep.1 hk).resolve_left h0
        rw [ite_eq_left hk, ite_eq_left]
        simpa [trip] using this
      · rw [ite_eq_right hk, ite_eq_right]
        intro hne; exact hk (hkeep.2 (Or.inr (by simpa [trip] using hne)))
  -- copy
  have g2 : ∀ r, (r < 70220 ∨ 70229 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [r₂ r (by omega) (by omega) (by omega), r₁ r (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  have q28 : c₂.nreg 70108 = 0 := by rw [g2 _ (by norm_num), r08]
  have hAc : c₂.nreg ALLOC = LB + 3 * (ddp (stl m₀ T B K) (0, 0, 0) j).length := by
    rw [g2 _ (by decide)]; rw [hI.alloc, hj]
  have hdl := ddp_length_le (stl m₀ T B K) (0, 0, 0) j
  have hlist := hI.list
  rw [hj] at hlist
  have h19 : c₂.nreg 70219 = (ddp (stl m₀ T B K) (0, 0, 0) j).length := by
    rw [g2 _ (by norm_num)]; rw [hI.cnt, hj]
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, m₃, l₃, n₃, q₃, rr₃, rm₃, o₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 70108 70228 dsCopy .skip) c₂ c₃ k₃ ∧ k₃ ≤ 9 ∧
      c₃.nreg ALLOC = LB + 3 * (ddp (stl m₀ T B K) (0, 0, 0) (j + 1)).length ∧
      (∀ a, a < LB + 3 * (ddp (stl m₀ T B K) (0, 0, 0) j).length → c₃.nmem a = c.nmem a) ∧
      ChordListAt c₃.nmem LB (ddp (stl m₀ T B K) (0, 0, 0) (j + 1)) ∧
      c₃.nreg 70219 = (ddp (stl m₀ T B K) (0, 0, 0) (j + 1)).length ∧
      (∀ r, r ≠ ALLOC → r ≠ 70219 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    rw [ddp_succ]
    by_cases hk : keep (stl m₀ T B K) (0, 0, 0) j = true
    · rw [ite_eq_left hk] at v2 ⊢
      obtain ⟨c₃, k₃, e₃, hk₃, a₃, mo, n0, n1, n2, n19, R₃, rr₃, rm₃, o₃⟩ := dsCopy_exec (P := P)
        c₂ e₂.wb_right hAc (by rw [g2 _ (by norm_num), r05]) (by omega) h19 (by omega)
      refine ⟨c₃, _, .ifLtN_true (by rwo [q28, v2]) e₃, by omega, ?_, fun a ha => ?_, ?_,
        by rws [n19, List.length_append], R₃, rr₃, rm₃, o₃⟩
      · rws [a₃, List.length_append]; ring
      · rw [mo a (Or.inl ha), m₂, m₁]
      · refine chordListAt_append (fun i hi => ?_) ?_ ?_ ?_
        · obtain ⟨b0, b1, b2⟩ := hlist i hi
          refine ⟨?_, ?_, ?_⟩
          · rwx [mo _ (Or.inl (by omega)), m₂, m₁]
          · rwx [mo _ (Or.inl (by omega)), m₂, m₁]
          · rwx [mo _ (Or.inl (by omega)), m₂, m₁]
        · rwr [n0, r₂ _ (by decide) (by decide) (by decide), v24, stl_getD ht, mT0, hx]
        · rw [n1, r₂ _ (by decide) (by decide) (by decide), v25, stl_getD ht, mT 1 (by omega),
            hx]; rfl
        · rw [n2, r₂ _ (by decide) (by decide) (by decide), v26, stl_getD ht, mT 2 (by omega),
            hx]; rfl
    · rw [ite_eq_right hk] at v2 ⊢
      rw [List.append_nil]
      refine ⟨c₂, _, .ifLtN_false (by rwo [q28, v2]) (.skip e₂.wb_right), by omega, hAc,
        fun a _ => by rw [m₂, m₁], ?_, h19, fun _ _ _ => rfl, rfl, rfl, rfl⟩
      rwx [m₂, m₁]
  -- advance
  have g3 : ∀ r, (r < 70219 ∨ 70229 < r) → r ≠ ALLOC → c₃.nreg r = c.nreg r := fun r hr ha => by
    rw [q₃ r ha (by omega), g2 r (by omega)]
  have q22 : c₃.nreg 70222 = x := by
    rwx [q₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide) (by decide)]
  have q21 : c₃.nreg 70221 = B + j := by
    rw [q₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide) (by decide),
      r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.cur, hj]
  have q20 : c₃.nreg 70220 = j := by
    rw [q₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide) (by decide),
      r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hj]
  have q05 : c₃.nreg 70105 = 1 := by rw [g3 _ (by norm_num) (by decide), r05]
  have w₃ := e₃.wb_right
  obtain ⟨c₄, k₄, e₄, hk₄, u23, u21, u20, r₄, m₄, rr₄, rm₄, o₄⟩ : ∃ c₄ k₄, Exec P W
      (block [.copyN 70223 70222, .addN 70221 70221 70105, .addN 70220 70220 70105]) c₃ c₄ k₄ ∧
      k₄ = 3 ∧ c₄.nreg 70223 = x ∧ c₄.nreg 70221 = B + (j + 1) ∧ c₄.nreg 70220 = j + 1 ∧
      (∀ r, r ≠ 70220 → r ≠ 70221 → r ≠ 70223 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem ∧
      c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, q21, q20, q05]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      q22, q21, q20, q05]
    all_goals ring
  have ex : Exec P W dsBody c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, _, ex, ⟨e₄.wb_right, by omega, by rw [u21, u20], fun _ => by rw [u23, u20, Nat.add_sub_cancel, hx],
    by rw [u20, ← a₃, r₄ _ (by decide) (by decide) (by decide)], by rwx [u20, m₄],
    by rw [u20, ← n₃, r₄ _ (by decide) (by decide) (by decide)],
    fun a ha => by rw [m₄, m₃ a (by omega), hI.low a ha],
    fun r hr ha => by rw [r₄ r (by omega) (by omega) (by omega), g3 r hr ha, hreg r hr ha],
    by rw [rr₄, rr₃, rr₂, rr₁, hI.rr], by rw [rm₄, rm₃, rm₂, rm₁, hI.rm],
    by rw [o₄, o₃, o₂, o₁, hI.out]⟩, by omega, by omega, by rw [u20, hj]⟩

/-- **The scan.** -/
theorem dsLoop_exec {P : Polygon} {W K T B LB : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70216 = T)
    (h30 : c₀.nreg 70230 = K)
    (hitems : ∀ j, j < K → m₀ (B + j) < K) (hTB : T + 3 * K ≤ LB) (hBL : B + K ≤ LB)
    (hW : LB + 3 * K + 3 ≤ W) :
    ∀ (n : ℕ) (c : Config), DSI W K T B LB m₀ c₀ c → c.nreg 70220 + n = K →
      ∃ c' k, Exec P W dsLoop c c' k ∧ k ≤ 60 * n + 2 ∧ 3 * n ≤ k ∧ DSI W K T B LB m₀ c₀ c' ∧
        c'.nreg 70220 = K
  | 0, c, hI, hn => by
    have h30' : c.nreg 70230 = K := by rw [hI.regs 70230 (by norm_num) (by decide), h30]
    exact ⟨c, 2, .whileLtN_false (by rwo [h30']) hI.wb, by omega, by omega, hI, by omega⟩
  | n + 1, c, hI, hn => by
    have h30' : c.nreg 70230 = K := by rw [hI.regs 70230 (by norm_num) (by decide), h30]
    have ht : c.nreg 70220 < K := by omega
    obtain ⟨c', k, e, hI', hk, hk3, hc'⟩ := dsBody_step (P := P) hI ht h05 h08 h16 hitems hTB hBL hW
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := dsLoop_exec h05 h08 h16 h30 hitems hTB hBL hW n c' hI'
      (by omega)
    exact ⟨c'', k + 2 + k₂, .whileLtN_true (by rwx [h30']) e e₂, by omega, by omega, hI'', hK⟩

end

end FuseAsm

end Chazelle.Core
