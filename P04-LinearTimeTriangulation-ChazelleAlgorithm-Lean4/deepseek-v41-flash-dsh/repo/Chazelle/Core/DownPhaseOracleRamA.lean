module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleCArc
public import Chazelle.Core.BruteRam2
public import Chazelle.Core.ShotListLeaf
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.NFBuildPassRam

/-!
# WP-M (E7-B, RAM part 1): the adapter's registers and its set-up

The interior oracles keep their state in band `bUp = 17` (registers `170000 …`), outside the
oracle bands, so that it survives the calls to the chain oracles (finding E7-B1); they write
`ioBands = insert bUp oracleBands`.

| reg | content |
|---|---|
| `170000 … 170009`, `170013` | the inputs of band `bShoot` / `bCut` (descriptor, subarc ends, origin, direction, `γ`, context handle) |
| `170010, 170011, 170012, 170018, 170019` | `n`, `1`, `0`, `2`, `n - 1` |
| `170014` | the orientation bit (`1` iff `LeftInside Q`) |
| `170015` | the host record `Host.whole n` (at the entry allocator `A₀`) |
| `170016, 170017` | the row table and the halving table of the grade table |

* `initI`: the saved inputs, the constants, the host record (four words at `A₀`, the allocator
  raised by `8`), and the running minimum flag `170070 := 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- **The bands of the interior oracles**: the oracle bands and the adapter's band `bUp`. -/
def ioBands : Finset ℕ := insert bUp oracleBands

theorem oracleBands_sub_io : oracleBands ⊆ ioBands := Finset.subset_insert _ _

/-- The saved inputs (band `b`, registers `b … b + 9`, `b + 13`). -/
def saveL (b : ℕ) : List (ℕ × ℕ) :=
  [(170000, b), (170001, b + 1), (170002, b + 2), (170003, b + 3), (170004, b + 4),
    (170005, b + 5), (170006, b + 6), (170007, b + 7), (170008, b + 8), (170009, b + 9),
    (170013, b + 13)]

/-- Saving the inputs. -/
def saveS (b : ℕ) : Stmt := block (SweepPrim.copies (saveL b))

theorem saveS_exec {P : Polygon} {W : ℕ} (b : ℕ) (hb : b + 13 < 170000) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c', Exec P W (saveS b) c c' 11 ∧ (∀ i, i < 10 → c'.nreg (170000 + i) = c.nreg (b + i)) ∧
      c'.nreg 170013 = c.nreg (b + 13) ∧
      (∀ r, ¬ (170000 ≤ r ∧ r < 170014) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := SweepPrim.copies_exec (P := P) (saveL b) c hw
    (by intro p hp q hq; simp only [saveL, List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> omega)
    (⊚ saveL)
  refine ⟨c', e, fun i hi => ?_, h1 (170013, b + 13) (⊚ saveL), fun r hr => h2 r ?_,
    h3, h4, h5, h6⟩
  · interval_cases i
    · exact h1 (170000, b) (⊚ saveL)
    · exact h1 (170001, b + 1) (⊚ saveL)
    · exact h1 (170002, b + 2) (⊚ saveL)
    · exact h1 (170003, b + 3) (⊚ saveL)
    · exact h1 (170004, b + 4) (⊚ saveL)
    · exact h1 (170005, b + 5) (⊚ saveL)
    · exact h1 (170006, b + 6) (⊚ saveL)
    · exact h1 (170007, b + 7) (⊚ saveL)
    · exact h1 (170008, b + 8) (⊚ saveL)
    · exact h1 (170009, b + 9) (⊚ saveL)
  · ϴ saveL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false
    omega

/-- The set-up: constants, the host record, the flag of the running minimum. -/
def initI : Stmt :=
  block [.inputSize 170010, .constN 170011 1, .constN 170012 0, .constN 170018 2,
    .subN 170019 170010 170011,
    .addN 170090 170000 170011, .loadN 170093 170090,
    .addN 170090 170013 170018, .loadN 170016 170090,
    .addN 170090 170090 170011, .loadN 170017 170090,
    .copyN 170015 9999,
    .storeN 170015 170011,
    .addN 170090 170015 170011, .storeN 170090 170012,
    .addN 170090 170090 170011, .storeN 170090 170012,
    .addN 170090 170090 170011, .storeN 170090 170019,
    .constN 170091 8, .addN 9999 9999 170091,
    .constN 170070 0]

/-- The orientation bit from the descriptor word: `1` iff the word is `1`. -/
def bitI : Stmt :=
  .ifLtN 170093 170011 (.instr (.constN 170014 0))
    (.ifLtN 170011 170093 (.instr (.constN 170014 0)) (.instr (.constN 170014 1)))

/-- The registers written by `initI` and `bitI`. -/
def BinitR (r : ℕ) : Prop :=
  r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170018 ∨ r = 170019 ∨ r = 170090 ∨ r = 170093 ∨
    r = 170016 ∨ r = 170017 ∨ r = 170015 ∨ r = 170091 ∨ r = 9999 ∨ r = 170070 ∨ r = 170014

/-- The registers written by `initI` and `bitI` (as a Boolean write set). -/
def BinitB (r : ℕ) : Bool :=
  decide (r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170018 ∨ r = 170019 ∨ r = 170090 ∨
    r = 170093 ∨ r = 170016 ∨ r = 170017 ∨ r = 170015 ∨ r = 170091 ∨ r = 9999 ∨ r = 170070 ∨
    r = 170014)

theorem wrM_initI : BuildRam.wrM BinitB initI = true := ⌖

/-- **The set-up.** -/
theorem initI_exec {P : Polygon} {W : ℕ} (c : Config)
    (hw : WordsBounded W c) (hMD : c.nreg 170000 + 1 ≤ W) (hh : c.nreg 170013 + 3 ≤ W)
    (hA : c.nreg ALLOC + 8 ≤ W) (hn : P.n ≤ W) (hn1 : 1 ≤ P.n) :
    ∃ c' k, Exec P W (.seq initI bitI) c c' k ∧ 22 ≤ k ∧ k ≤ 27 ∧
      c'.nreg 170010 = P.n ∧ c'.nreg 170011 = 1 ∧
      c'.nreg 170012 = 0 ∧ c'.nreg 170018 = 2 ∧ c'.nreg 170019 = P.n - 1 ∧
      c'.nreg 170016 = c.nmem (c.nreg 170013 + 2) ∧
      c'.nreg 170017 = c.nmem (c.nreg 170013 + 3) ∧
      (c'.nreg 170014 = 1 ↔ c.nmem (c.nreg 170000 + 1) = 1) ∧ c'.nreg 170014 ≤ 1 ∧
      c'.nreg 170015 = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧
      c'.nreg 170070 = 0 ∧
      c'.nmem (c.nreg ALLOC) = 1 ∧ c'.nmem (c.nreg ALLOC + 1) = 0 ∧
      c'.nmem (c.nreg ALLOC + 2) = 0 ∧ c'.nmem (c.nreg ALLOC + 3) = P.n - 1 ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ BinitR r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, q12, q18, q19, q16, q17, q93, q15, qA, q70, m0, m1, m2, m3,
      mlo, rest, rr, rm, ro⟩ : ∃ c₁ k₁, Exec P W initI c c₁ k₁ ∧ k₁ = 22 ∧
      c₁.nreg 170010 = P.n ∧ c₁.nreg 170011 = 1 ∧
      c₁.nreg 170012 = 0 ∧ c₁.nreg 170018 = 2 ∧ c₁.nreg 170019 = P.n - 1 ∧
      c₁.nreg 170016 = c.nmem (c.nreg 170013 + 2) ∧
      c₁.nreg 170017 = c.nmem (c.nreg 170013 + 3) ∧
      c₁.nreg 170093 = c.nmem (c.nreg 170000 + 1) ∧
      c₁.nreg 170015 = c.nreg 9999 ∧ c₁.nreg 9999 = c.nreg 9999 + 8 ∧
      c₁.nreg 170070 = 0 ∧
      c₁.nmem (c.nreg 9999) = 1 ∧ c₁.nmem (c.nreg 9999 + 1) = 0 ∧
      c₁.nmem (c.nreg 9999 + 2) = 0 ∧ c₁.nmem (c.nreg 9999 + 3) = P.n - 1 ∧
      (∀ a, a < c.nreg 9999 → c₁.nmem a = c.nmem a) ∧
      True ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
      c₁.output = c.output := by
    unfold initI
    exec_block
    all_goals first | omega | (config_simp; omega) | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, ?_, ?_, ?_, ?_, fun a ha => ?_, trivial, rfl, rfl, rfl⟩
    · simp only [Config.nmem_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nmem_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nmem_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nmem_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nmem_mk, upd]; split_ifs <;> first | rfl | omega
  have fM := BuildRam.exec_frameM e₁ wrM_initI
  replace rest : ∀ r, ¬ BinitR r → c₁.nreg r = c.nreg r := fun r hr =>
    fM.1 r (by unfold BinitB; unfold BinitR at hr; simpa using hr)
  have w₁ := e₁.wb_right
  have hb : c₁.nreg 170011 = 1 := q11
  -- the orientation bit
  obtain ⟨c₂, k₂, e₂, hk₂, b14, bl, r₂⟩ : ∃ c₂ k₂, Exec P W bitI c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
      (c₂.nreg 170014 = 1 ↔ c₁.nreg 170093 = 1) ∧ c₂.nreg 170014 ≤ 1 ∧
      c₂ = { c₁ with nreg := upd c₁.nreg 170014 (c₂.nreg 170014) } := by
    unfold bitI
    by_cases h1 : c₁.nreg 170093 < c₁.nreg 170011
    · refine ⟨_, _, .ifLtN_true h1 (Exec.constN w₁ 170014 0 (by omega)), by omega, ?_, ?_, ?_⟩
      · simp only [upd_same]; omega
      · simp only [upd_same]; omega
      · simp only [upd_same]
    by_cases h2 : c₁.nreg 170011 < c₁.nreg 170093
    · refine ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 (Exec.constN w₁ 170014 0 (by omega))),
        by omega, ?_, ?_, ?_⟩
      · simp only [upd_same]; omega
      · simp only [upd_same]; omega
      · simp only [upd_same]
    · refine ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.constN w₁ 170014 1 (by omega))),
        by omega, ?_, ?_, ?_⟩
      · simp only [upd_same]; exact ⟨fun _ => by omega, fun _ => trivial⟩
      · simp only [upd_same]; omega
      · simp only [upd_same]
  have k : ∀ r, r ≠ 170014 → c₂.nreg r = c₁.nreg r := fun r hr => by
    rw [r₂]; simp [upd, hr]
  refine ⟨c₂, _, .seq e₁ e₂, by omega, by omega, by rw [k _ (by omega)]; exact q10,
    by rw [k _ (by omega)]; exact q11, by rw [k _ (by omega)]; exact q12,
    by rw [k _ (by omega)]; exact q18, by rw [k _ (by omega)]; exact q19,
    by rw [k _ (by omega)]; exact q16, by rw [k _ (by omega)]; exact q17,
    by rw [b14, q93], bl, by rw [k _ (by omega)]; exact q15, by rw [k _ (by omega)]; exact qA,
    by rw [k _ (by omega)]; exact q70, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [r₂]; simp only [Config.nmem_mk]; first | exact m0 | exact m1 | exact m2 | exact m3)
    | skip
  · rw [r₂]; exact mlo a ha
  · rw [k r (by unfold BinitR at hr; omega)]; exact rest r hr
  · rw [r₂]; exact rr
  · rw [r₂]; exact rm
  · rw [r₂]; exact ro

end

end IOrc

end Chazelle.Core
