module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvTC0
public import Chazelle.Core.DownPhaseBaseLoop1

/-!
# Down-phase transition (D2), RAM part 3: the filter pass

`fLoop` runs over the `K₀` chord records of the normal form of the top chain (chord area at
`CB`, five words per record): it reads `(h, lp, rp)`, tests the two ends (`fTest`, the index
test `innerE`), maps them (`fMap`, `mapE`) and appends the mapped triple of a kept record
(`keepT`) at the write cursor (`fKeep`).  After `i` records the list area at `B'` holds the
first `rank i` triples of `transL` (`memT`).  Invariant `FInv`, loop lemma `fLoop_exec`.

Registers (band `19`): `190010 = m`, `190014 = c₀`, `190015 = c₀ + m`, `190016 = idxI 0`,
`190017 = 1`, `190018 = 0`, `190023 = K₀`; loop: `190030` record index, `190031` read cursor,
`190032 … 190034` the triple, `190035` write cursor, `190036` kept count, `190037` flag,
`190038, 190039` the mapped ends.
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)

@[expose] public section

/-! ## The program -/

/-- Load the triple of the record at the read cursor and advance it by `5`; clear the flag. -/
def fLoad : Stmt := block [.loadN 190032 190031, .addN 190031 190031 190017,
  .loadN 190033 190031, .addN 190031 190031 190017, .loadN 190034 190031,
  .addN 190031 190031 190017, .addN 190031 190031 190017, .addN 190031 190031 190017,
  .constN 190037 0]

/-- Raise the flag if the end in register `p` is inner. -/
def fTest (p : ℕ) : Stmt :=
  .ifLtN p 190014 .skip
    (.ifLtN p 190015
      (.ifLtN 190014 p (.instr (.constN 190037 1))
        (.ifLtN 190032 190016 (.instr (.constN 190037 1))
          (.ifLtN 190016 190032 (.instr (.constN 190037 1)) .skip)))
      .skip)

/-- Map the end in register `p` into register `d`. -/
def fMap (d p : ℕ) : Stmt :=
  .seq (.instr (.copyN d 190010))
    (.ifLtN p 190014 .skip (.ifLtN p 190015 (.instr (.subN d p 190014)) .skip))

/-- Append the mapped triple. -/
def fKeep : Stmt := block [.storeN 190035 190032, .addN 190035 190035 190017,
  .storeN 190035 190038, .addN 190035 190035 190017, .storeN 190035 190039,
  .addN 190035 190035 190017, .addN 190036 190036 190017]

/-- One record. -/
def fBody : Stmt :=
  .seq fLoad (.seq (fTest 190033) (.seq (fTest 190034) (.seq (fMap 190038 190033)
    (.seq (fMap 190039 190034) (.seq (.ifLtN 190018 190037 fKeep .skip)
      (.instr (.addN 190030 190030 190017)))))))

/-- **The filter pass.** -/
def fLoop : Stmt := .whileLtN 190030 190023 fBody

/-! ## The memory of the pass -/

/-- The memory after `i` records: the kept triples so far at `B'`, mapped. -/
def memT (m₀ : ℕ → ℕ) (li : Bool) (n c₀ : ℕ) (L₀ : List (ℕ × ℕ × ℕ)) (B' i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF (keepT li n c₀) L₀ i then tw (transL li n c₀ L₀) (a - B')
  else m₀ a

/-- The kept triple of record `i` is entry `rank i` of the filtered list. -/
theorem getD_transL {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {i : ℕ}
    (hi : i < L₀.length) (hk : keepT li n c₀ (L₀.getD i (0, 0, 0)) = true) :
    (transL li n c₀ L₀).getD (rankF (keepT li n c₀) L₀ i) (0, 0, 0) =
      trT n c₀ (L₀.getD i (0, 0, 0)) := by
  have hlt := DownBase.rankF_lt_length (keepT li n c₀) (0, 0, 0) hi hk
  have hg := DownBase.getD_filter_rank (keepT li n c₀) (0, 0, 0) hi hk
  unfold transL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, ← hg, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt, Option.getD_some]

/-- The memory step of a kept record. -/
theorem memT_keep {m₀ m : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' i : ℕ}
    (hm : ∀ a, m a = memT m₀ li n c₀ L₀ B' i a) (hi : i < L₀.length)
    (hk : keepT li n c₀ (L₀.getD i (0, 0, 0)) = true) (a : ℕ) :
    (if a = B' + 3 * rankF (keepT li n c₀) L₀ i + 2 then (trT n c₀ (L₀.getD i (0, 0, 0))).2.2
      else if a = B' + 3 * rankF (keepT li n c₀) L₀ i + 1 then
        (trT n c₀ (L₀.getD i (0, 0, 0))).2.1
      else if a = B' + 3 * rankF (keepT li n c₀) L₀ i then (trT n c₀ (L₀.getD i (0, 0, 0))).1
      else m a) = memT m₀ li n c₀ L₀ B' (i + 1) a := by
  have hr := DownBase.rankF_succ (keepT li n c₀) (0, 0, 0) hi
  rw [ite_eq_left hk] at hr
  set j := rankF (keepT li n c₀) L₀ i with hj
  have hg := getD_transL hi hk
  rw [← hj] at hg
  have htw : ∀ s, s < 3 → tw (transL li n c₀ L₀) (3 * j + s) =
      if s = 0 then (trT n c₀ (L₀.getD i (0, 0, 0))).1
      else if s = 1 then (trT n c₀ (L₀.getD i (0, 0, 0))).2.1
      else (trT n c₀ (L₀.getD i (0, 0, 0))).2.2 := fun s hs => by
    unfold tw
    rw [show (3 * j + s) % 3 = s by omega, show (3 * j + s) / 3 = j by omega, hg]
  rw [hm a]
  unfold memT
  rw [hr]
  by_cases h3 : a = B' + 3 * j + 2
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 (by norm_num)]
    try simp
  by_cases h4 : a = B' + 3 * j + 1
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 (by norm_num)]
    try simp
  by_cases h5 : a = B' + 3 * j
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left (by omega),
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 (by norm_num)]
    try simp
  rw [ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]
  split_ifs <;> first | rfl | omega

/-- The memory of a dropped record does not change. -/
theorem memT_drop {m₀ : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' i : ℕ}
    (hi : i < L₀.length) (hk : keepT li n c₀ (L₀.getD i (0, 0, 0)) = false) (a : ℕ) :
    memT m₀ li n c₀ L₀ B' i a = memT m₀ li n c₀ L₀ B' (i + 1) a := by
  have hr := DownBase.rankF_succ (keepT li n c₀) (0, 0, 0) hi
  rw [hk] at hr
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
  unfold memT; rw [hr]

/-! ## The pieces of one record -/

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem fLoad_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (h31 : c.nreg 190031 = a)
    (h17 : c.nreg 190017 = 1) (haW : a + 5 ≤ W) :
    ∃ c' k, Exec P W fLoad c c' k ∧ k = 9 ∧ c'.nreg 190032 = c.nmem a ∧
      c'.nreg 190033 = c.nmem (a + 1) ∧ c'.nreg 190034 = c.nmem (a + 2) ∧
      c'.nreg 190031 = a + 5 ∧ c'.nreg 190037 = 0 ∧
      (∀ r, r ≠ 190031 → r ≠ 190032 → r ≠ 190033 → r ≠ 190034 → r ≠ 190037 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold fLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h31, h17]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h31, h17]

/-- **The test of an end.** -/
theorem fTest_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) {li : Bool} {n c₀ p : ℕ}
    (_hp : p ≠ 190037) (_hp1 : p ≠ 190014) (_hp2 : p ≠ 190015)
    (h14 : c.nreg 190014 = c₀) (h15 : c.nreg 190015 = c₀ + (n - 1))
    (h16 : c.nreg 190016 = idxI li n 0) :
    ∃ c' k, Exec P W (fTest p) c c' k ∧ k ≤ 10 ∧
      c'.nreg 190037 = (if innerE li n c₀ (c.nreg 190032) (c.nreg p) = true then 1
        else c.nreg 190037) ∧
      (∀ r, r ≠ 190037 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∃ c' k, Exec P W (.instr (.constN 190037 1)) c c' k ∧ k = 1 ∧
      c'.nreg 190037 = 1 ∧ (∀ r, r ≠ 190037 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
    ⟨_, _, Exec.constN hw 190037 1 hW, rfl, ✓, fun r hr => by simp [hr], rfl, rfl, rfl,
      rfl⟩
  obtain ⟨cs, ks, es, hks, vs, gs, ms, rrs, rms, os⟩ := hset
  unfold fTest innerE
  by_cases h1 : c.nreg p < c.nreg 190014
  · refine ⟨c, _, .ifLtN_true h1 (.skip hw), ⋄, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    Ξ ite_eq_right (by rw [h14] at h1; simp; omega)
  by_cases h2 : c.nreg p < c.nreg 190015
  · by_cases h3 : c.nreg 190014 < c.nreg p
    · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_true h3 es)), ⋄, ?_, gs,
        ms, rrs, rms, os⟩
      Ξ vs, ite_eq_left (by rw [h14] at h1 h3; rw [h15] at h2; simp; omega)
    · by_cases h4 : c.nreg 190032 < c.nreg 190016
      · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_true h4 es))),
          ⋄, ?_, gs, ms, rrs, rms, os⟩
        rw [h14] at h1 h3; rw [h15] at h2; rw [h16] at h4
        rw [vs, ite_eq_left (decide_eq_true ⟨⋄, by omega, fun ⟨_, he⟩ => by omega⟩)]
      · by_cases h5 : c.nreg 190016 < c.nreg 190032
        · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_false h4
            (.ifLtN_true h5 es)))), ⋄, ?_, gs, ms, rrs, rms, os⟩
          rw [h14] at h1 h3; rw [h15] at h2; rw [h16] at h5
          rw [vs, ite_eq_left (decide_eq_true ⟨⋄, by omega, fun ⟨_, he⟩ => by omega⟩)]
        · refine ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_false h4
            (.ifLtN_false h5 (.skip hw))))), ⋄, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
          Ξ ite_eq_right (by rw [h14] at h1 h3; rw [h15] at h2; rw [h16] at h4 h5; simp; omega)
  · refine ⟨c, _, .ifLtN_false h1 (.ifLtN_false h2 (.skip hw)), ⋄, ?_, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
    Ξ ite_eq_right (by rw [h15] at h2; simp; omega)

/-- **The map of an end.** -/
theorem fMap_exec (c : Config) (hw : WordsBounded W c) {n c₀ d p : ℕ}
    (hd1 : d ≠ 190014) (hd2 : d ≠ 190015) (hdp : d ≠ p) (_hd3 : d ≠ 190010)
    (h10 : c.nreg 190010 = n - 1) (h14 : c.nreg 190014 = c₀)
    (h15 : c.nreg 190015 = c₀ + (n - 1)) :
    ∃ c' k, Exec P W (fMap d p) c c' k ∧ k ≤ 6 ∧ c'.nreg d = mapE n c₀ (c.nreg p) ∧
      (∀ r, r ≠ d → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.copyN (P := P) hw d 190010
  set c₁ : Config := { c with nreg := upd c.nreg d (c.nreg 190010) } with hc₁
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, r ≠ d → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [hr]
  have v₁ : c₁.nreg d = n - 1 := by rw [hc₁]; simp [h10]
  have q14 : c₁.nreg 190014 = c₀ := Ρ g₁ _ (Ne.symm hd1), h14
  have q15 : c₁.nreg 190015 = c₀ + (n - 1) := Ρ g₁ _ (Ne.symm hd2), h15
  have qp : c₁.nreg p = c.nreg p := g₁ _ (Ne.symm hdp)
  unfold fMap mapE
  by_cases h1 : c₁.nreg p < c₁.nreg 190014
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_true h1 (.skip w₁)), ⋄, ?_, g₁, rfl, rfl, rfl, rfl⟩
    Ξ v₁, ite_eq_right (by rw [q14, qp] at h1; omega)
  by_cases h2 : c₁.nreg p < c₁.nreg 190015
  · have e₂ := Exec.subN (P := P) w₁ d p 190014
    refine ⟨_, _, .seq e₁ (.ifLtN_false h1 (.ifLtN_true h2 e₂)), ⋄, ?_,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · ϴ Machine.upd_same
      Ξ qp, q14, ite_eq_left (by rw [q14, qp] at h1; rw [q15, qp] at h2; omega)
    · simp only; rw [Machine.upd_other _ _ _ hr]; exact g₁ r hr
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_false h1 (.ifLtN_false h2 (.skip w₁))), ⋄, ?_, g₁,
      rfl, rfl, rfl, rfl⟩
    Ξ v₁, ite_eq_right (by rw [q15, qp] at h2; omega)

set_option maxHeartbeats 4000000 in
/-- **Append a triple.** -/
theorem fKeep_exec (c : Config) (hw : WordsBounded W c) {w j : ℕ} (h35 : c.nreg 190035 = w)
    (h36 : c.nreg 190036 = j) (h17 : c.nreg 190017 = 1) (hwW : w + 3 ≤ W) (hjW : j + 1 ≤ W) :
    ∃ c' k, Exec P W fKeep c c' k ∧ k = 7 ∧ c'.nreg 190035 = w + 3 ∧ c'.nreg 190036 = j + 1 ∧
      (∀ r, r ≠ 190035 → r ≠ 190036 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = w + 2 then c.nreg 190039 else if a = w + 1 then c.nreg 190038
        else if a = w then c.nreg 190032 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fKeep
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h35, h36, h17]; omega)
  refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h35, h36, h17]
  all_goals (try simp only [Machine.upd_apply])

end exec

end

end DrvT

end Chazelle.Core
