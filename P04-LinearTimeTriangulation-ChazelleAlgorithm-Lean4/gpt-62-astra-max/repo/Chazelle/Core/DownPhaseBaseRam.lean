module

public import Chazelle.Core.DownPhaseBaseList
public import Chazelle.Core.SortRam

/-!
# Down phase, A1 (RAM, part 1): the program and the pieces of the chord pass

`dropStmt` (band `bDown`, registers `200000 + i`):
* inputs `200000` descriptor `D` (word `D + 1`: the `LeftInside` bit), `200001` chord list `B`,
  `200002` its length `K`, `200003` event list `SE`;
* outputs `200004` new chord list `B' = ALLOC`, `200005` its length `K'`, `200006` new event list
  `SE' = B' + 5K`; the code table lies at `X = B' + 3K`; the allocator ends at `B' + 7K`.

Scratch: `200100 = 1`, `200101 = 0`, `200102 = n`, `200103` the normalised `LeftInside` bit,
`200104 = n - 1`, `200105 = 2`, `200106` the raw bit; pass 1: `200110` chord, `200111` read
cursor, `200112 … 200114` the triple, `200115` flag, `200116` start vertex, `200117` table
cursor, `200118` kept count, `200119` write cursor, `200120` code; `200121 = X`, `200122 = SE'`;
pass 2: `200130` event, `200131` read cursor, `200132` code, `200133` table word, `200134` write
cursor, `200135` address, `200136 = 2K`.

This file: the program, the memory of pass 1 (`mem1`), and the pieces of one chord.
Design: `docs/design-downphase-nf.md` §3.4.
-/

namespace Chazelle.Core

namespace DownBase

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- Constants, allocation, pass-1 cursors. -/
def dSetup : Stmt := block [.constN 200100 1, .constN 200101 0, .constN 200105 2,
  .inputSize 200102, .subN 200104 200102 200100, .addN 200116 200000 200100,
  .loadN 200106 200116, .constN 200103 0, .addN 200136 200002 200002, .copyN 200004 9999,
  .copyN 200121 9999, .addN 200121 200121 200002, .addN 200121 200121 200002,
  .addN 200121 200121 200002, .addN 200122 200121 200136, .addN 9999 200122 200136,
  .copyN 200006 200122, .constN 200110 0, .copyN 200111 200001, .copyN 200117 200121,
  .constN 200118 0, .copyN 200119 200004]

/-- The normalised bit: `1` iff the raw bit is `1`. -/
def dBit : Stmt :=
  .ifLtN 200106 200105 (.ifLtN 200101 200106 (.instr (.constN 200103 1)) .skip) .skip

/-- Load the triple; clear the flag. -/
def dLoad : Stmt := block [.loadN 200112 200111, .addN 200111 200111 200100,
  .loadN 200113 200111, .addN 200111 200111 200100, .loadN 200114 200111,
  .addN 200111 200111 200100, .constN 200115 0]

/-- Raise the flag if the height vertex starts the walk edge in register `p`. -/
def dTest (p : ℕ) : Stmt :=
  .seq (.ifLtN 200101 200103 (.instr (.copyN 200116 p)) (.instr (.subN 200116 200104 p)))
    (.ifLtN 200112 200116 .skip (.ifLtN 200116 200112 .skip (.instr (.constN 200115 1))))

/-- A kept chord: append the triple, table entries `2j + 1`, `2j + 2`. -/
def dKeep : Stmt := block [.storeN 200119 200112, .addN 200119 200119 200100,
  .storeN 200119 200113, .addN 200119 200119 200100, .storeN 200119 200114,
  .addN 200119 200119 200100, .addN 200120 200118 200118, .addN 200120 200120 200100,
  .storeN 200117 200120, .addN 200117 200117 200100, .addN 200120 200120 200100,
  .storeN 200117 200120, .addN 200117 200117 200100, .addN 200118 200118 200100]

/-- A dropped chord: table entries `0, 0`. -/
def dDrop : Stmt := block [.storeN 200117 200101, .addN 200117 200117 200100,
  .storeN 200117 200101, .addN 200117 200117 200100]

/-- One chord. -/
def dBody1 : Stmt :=
  .seq dLoad (.seq (dTest 200113) (.seq (dTest 200114)
    (.seq (.ifLtN 200101 200115 dKeep dDrop) (.instr (.addN 200110 200110 200100)))))

/-- The chord pass. -/
def dLoop1 : Stmt := .whileLtN 200110 200002 dBody1

/-- Between the passes. -/
def dMid : Stmt := block [.copyN 200005 200118, .constN 200130 0, .copyN 200131 200003,
  .copyN 200134 200122]

/-- One event. -/
def dBody2 : Stmt :=
  .seq (block [.loadN 200132 200131, .addN 200131 200131 200100, .addN 200135 200121 200132,
      .loadN 200133 200135])
    (.seq (.ifLtN 200101 200133 (block [.subN 200133 200133 200100, .storeN 200134 200133,
      .addN 200134 200134 200100]) .skip) (.instr (.addN 200130 200130 200100)))

/-- The event pass. -/
def dLoop2 : Stmt := .whileLtN 200130 200136 dBody2

/-- **The procedure of `DropAugSpec`.** -/
def dropStmt : Stmt := .seq dSetup (.seq dBit (.seq dLoop1 (.seq dMid dLoop2)))

/-! ## The memory of the chord pass -/

/-- Word `q` of a triple list. -/
def tw (L' : List (ℕ × ℕ × ℕ)) (q : ℕ) : ℕ :=
  if q % 3 = 0 then (L'.getD (q / 3) (0, 0, 0)).1
  else if q % 3 = 1 then (L'.getD (q / 3) (0, 0, 0)).2.1 else (L'.getD (q / 3) (0, 0, 0)).2.2

/-- The code table: new code plus one, or `0` for a dropped chord. -/
def tbl (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (q : ℕ) : ℕ :=
  if keptC li n L q then newCode li n L q + 1 else 0

/-- The memory after `i` chords. -/
def mem1 (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (B' X i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF (keepX li n) L i then tw (keepL li n L) (a - B')
  else if X ≤ a ∧ a < X + 2 * i then tbl li n L (a - X) else m₀ a

theorem rankF_le (f : ℕ × ℕ × ℕ → Bool) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : rankF f L i ≤ i := by
  unfold rankF
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The memory step of a kept chord. -/
theorem mem1_keep {m₀ m : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i : ℕ}
    (hm : ∀ a, m a = mem1 m₀ li n L B' X i a) (hi : i < L.length) (hBX : B' + 3 * L.length ≤ X)
    (hk : keepX li n (L.getD i (0, 0, 0)) = true) (a : ℕ) :
    (if a = X + 2 * i + 1 then 2 * rankF (keepX li n) L i + 2
      else if a = X + 2 * i then 2 * rankF (keepX li n) L i + 1
      else if a = B' + 3 * rankF (keepX li n) L i + 2 then (L.getD i (0, 0, 0)).2.2
      else if a = B' + 3 * rankF (keepX li n) L i + 1 then (L.getD i (0, 0, 0)).2.1
      else if a = B' + 3 * rankF (keepX li n) L i then (L.getD i (0, 0, 0)).1 else m a) =
      mem1 m₀ li n L B' X (i + 1) a := by
  have hr := rankF_succ (keepX li n) (0, 0, 0) hi
  rw [ite_eq_left hk] at hr
  have hle := rankF_le (keepX li n) L i
  set j := rankF (keepX li n) L i with hj
  have hg := getD_keepL (li := li) (n := n) hi hk
  rw [← hj] at hg
  have hkc : ∀ s, s < 2 → keptC li n L (2 * i + s) = true := fun s hs => by
    unfold keptC; rw [show (2 * i + s) / 2 = i by omega]; exact hk
  have hnc : ∀ s, s < 2 → newCode li n L (2 * i + s) = 2 * j + s := fun s hs => by
    unfold newCode; rw [show (2 * i + s) / 2 = i by omega, ← hj]; omega
  rw [hm a]
  unfold mem1
  rw [hr]
  by_cases h1 : a = X + 2 * i + 1
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega), show X + 2 * i + 1 - X = 2 * i + 1 by
      omega, tbl, ite_eq_left (hkc 1 (by norm_num)), hnc 1 (by norm_num)]
  by_cases h2 : a = X + 2 * i
  · subst h2
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega), show X + 2 * i - X = 2 * i by
      omega, tbl, show 2 * i = 2 * i + 0 by rfl, ite_eq_left (hkc 0 (by norm_num)),
      hnc 0 (by norm_num)]
  rw [ite_eq_right h1, ite_eq_right h2]
  have htw : ∀ s, s < 3 → tw (keepL li n L) (3 * j + s) =
      if s = 0 then (L.getD i (0, 0, 0)).1 else if s = 1 then (L.getD i (0, 0, 0)).2.1
      else (L.getD i (0, 0, 0)).2.2 := fun s hs => by
    unfold tw
    rw [show (3 * j + s) % 3 = s by omega, show (3 * j + s) / 3 = j by omega, hg]
  by_cases h3 : a = B' + 3 * j + 2
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 (by norm_num)]
    simp
  by_cases h4 : a = B' + 3 * j + 1
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 (by norm_num)]
    simp
  by_cases h5 : a = B' + 3 * j
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left (by omega),
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 (by norm_num)]
    simp
  rw [ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]
  split_ifs <;> first | rfl | omega

/-- The memory step of a dropped chord. -/
theorem mem1_drop {m₀ m : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i : ℕ}
    (hm : ∀ a, m a = mem1 m₀ li n L B' X i a) (hi : i < L.length) (hBX : B' + 3 * L.length ≤ X)
    (hk : keepX li n (L.getD i (0, 0, 0)) = false) (a : ℕ) :
    (if a = X + 2 * i + 1 then 0 else if a = X + 2 * i then 0 else m a) =
      mem1 m₀ li n L B' X (i + 1) a := by
  have hr := rankF_succ (keepX li n) (0, 0, 0) hi
  rw [hk] at hr
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
  have hle := rankF_le (keepX li n) L i
  have hkc : ∀ s, s < 2 → keptC li n L (2 * i + s) = false := fun s hs => by
    unfold keptC; rw [show (2 * i + s) / 2 = i by omega]; exact hk
  rw [hm a]
  unfold mem1
  rw [hr]
  by_cases h1 : a = X + 2 * i + 1
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega), show X + 2 * i + 1 - X = 2 * i + 1 by
      omega, tbl, hkc 1 (by norm_num)]
    simp
  by_cases h2 : a = X + 2 * i
  · subst h2
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega), show X + 2 * i - X = 2 * i + 0
      by omega, tbl, hkc 0 (by norm_num)]
    simp
  rw [ite_eq_right h1, ite_eq_right h2]
  by_cases h6 : B' ≤ a ∧ a < B' + 3 * rankF (keepX li n) L i
  · rw [ite_eq_left h6, ite_eq_left h6]
  · rw [ite_eq_right h6, ite_eq_right h6]
    by_cases h7 : X ≤ a ∧ a < X + 2 * i
    · rw [ite_eq_left h7, ite_eq_left (by omega)]
    · rw [ite_eq_right h7, ite_eq_right (by omega)]

/-! ## The pieces of one chord -/

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem dLoad_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (h111 : c.nreg 200111 = a)
    (h100 : c.nreg 200100 = 1) (haW : a + 3 ≤ W) :
    ∃ c' k, Exec P W dLoad c c' k ∧ k = 7 ∧ c'.nreg 200112 = c.nmem a ∧
      c'.nreg 200113 = c.nmem (a + 1) ∧ c'.nreg 200114 = c.nmem (a + 2) ∧
      c'.nreg 200111 = a + 3 ∧ c'.nreg 200115 = 0 ∧
      (∀ r, r ≠ 200111 → r ≠ 200112 → r ≠ 200113 → r ≠ 200114 → r ≠ 200115 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h111, h100]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h111, h100]

/-- The equality test of the flag. -/
theorem dEq_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (.ifLtN 200112 200116 .skip (.ifLtN 200116 200112 .skip
        (.instr (.constN 200115 1)))) c c' k ∧ k ≤ 5 ∧
      c'.nreg 200115 = (if c.nreg 200112 = c.nreg 200116 then 1 else c.nreg 200115) ∧
      (∀ r, r ≠ 200115 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases h1 : c.nreg 200112 < c.nreg 200116
  · exact ⟨c, _, .ifLtN_true h1 (.skip hw), by omega, by rw [ite_eq_right (by omega)],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  by_cases h2 : c.nreg 200116 < c.nreg 200112
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw)), by omega,
      by rw [ite_eq_right (by omega)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have e := Exec.constN (P := P) hw 200115 1 hW
  exact ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 e), by omega, by simp [show c.nreg 200112 =
    c.nreg 200116 by omega], fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

/-- **The start-vertex test.** -/
theorem dTest_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) {li : Bool} {n p : ℕ}
    (_hp1 : p ≠ 200116) (h101 : c.nreg 200101 = 0)
    (hbit : c.nreg 200103 = if li then 1 else 0) (h104 : c.nreg 200104 = n - 1) :
    ∃ c' k, Exec P W (dTest p) c c' k ∧ k ≤ 8 ∧
      c'.nreg 200115 = (if c.nreg 200112 = wStart li n (c.nreg p) then 1 else c.nreg 200115) ∧
      (∀ r, r ≠ 200115 → r ≠ 200116 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (.ifLtN 200101 200103 (.instr (.copyN 200116 p)) (.instr (.subN 200116 200104 p))) c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 200116 = wStart li n (c.nreg p) ∧
      (∀ r, r ≠ 200116 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    cases li
    · have h : ¬ c.nreg 200101 < c.nreg 200103 := by rw [h101, hbit]; simp
      exact ⟨_, _, .ifLtN_false h (Exec.subN hw 200116 200104 p), by omega,
        by simp [wStart, h104], fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
    · have h : c.nreg 200101 < c.nreg 200103 := by rw [h101, hbit]; simp
      exact ⟨_, _, .ifLtN_true h (Exec.copyN hw 200116 p), by omega,
        by simp [wStart], fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dEq_exec (P := P) c₁ e₁.wb_right hW
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, fun r a b => by rw [r₂ r a, r₁ r b], by rw [m₂, m₁],
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [v₂, v₁, r₁ _ (by norm_num), r₁ _ (by norm_num)]

set_option maxHeartbeats 4000000 in
/-- **A kept chord.** -/
theorem dKeep_exec (c : Config) (hw : WordsBounded W c) {w x j : ℕ} (h119 : c.nreg 200119 = w)
    (h117 : c.nreg 200117 = x) (h118 : c.nreg 200118 = j) (h100 : c.nreg 200100 = 1)
    (hwW : w + 3 ≤ W) (hxW : x + 2 ≤ W) (hjW : 2 * j + 2 ≤ W) :
    ∃ c' k, Exec P W dKeep c c' k ∧ k = 14 ∧ c'.nreg 200119 = w + 3 ∧
      c'.nreg 200117 = x + 2 ∧ c'.nreg 200118 = j + 1 ∧
      (∀ r, r ≠ 200117 → r ≠ 200118 → r ≠ 200119 → r ≠ 200120 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = x + 1 then 2 * j + 2 else if a = x then 2 * j + 1
        else if a = w + 2 then c.nreg 200114 else if a = w + 1 then c.nreg 200113
        else if a = w then c.nreg 200112 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dKeep
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h119, h117, h118, h100]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h119, h117, h118, h100]
  simp only [Machine.upd_apply]
  congr 1 <;> (try ring_nf)

set_option maxHeartbeats 4000000 in
/-- **A dropped chord.** -/
theorem dDrop_exec (c : Config) (hw : WordsBounded W c) {x : ℕ} (h117 : c.nreg 200117 = x)
    (h100 : c.nreg 200100 = 1) (h101 : c.nreg 200101 = 0) (hxW : x + 2 ≤ W) :
    ∃ c' k, Exec P W dDrop c c' k ∧ k = 4 ∧ c'.nreg 200117 = x + 2 ∧
      (∀ r, r ≠ 200117 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = x + 1 then 0 else if a = x then 0 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dDrop
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h117, h100]; omega)
  refine ⟨rfl, ?_, fun r a1 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h117, h100, h101]
  simp only [Machine.upd_apply]

end exec

end

end DownBase

end Chazelle.Core
