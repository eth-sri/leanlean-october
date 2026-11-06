module

public meta import Chazelle.Arithmetic

public import Chazelle.Spec

/-!
# Machine basics

Elementary lemmas about the exact real RAM of `Chazelle/Spec.lean`:

* `upd` (register/memory update) lemmas;
* one lemma per instruction describing `step` when that instruction is at the
  program counter (`step_halt`, `step_constN`, …, `step_divR`, `step_divR_zero`);
* `run` lemmas (`run_zero`, `run_succ`, `run_add`, `run_succ_right`,
  `run_eq_some_of_le`, …);
* monotonicity of `WordsBounded` and `RunsWithin`;
* frame lemmas: what a `step` leaves unchanged;
* `BoundedRun` / `RunsTo`, the "every visited configuration is word-bounded"
  predicates used to build `RunsWithin` compositionally.
-/

namespace Chazelle

namespace Machine

@[expose] public section

/-! ### `upd` -/

@[simp] theorem upd_same {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : upd f i v i = v := by
  simp [upd]

section
variable {α : Type} (f : ℕ → α) (i : ℕ)
include α
@[simp] theorem upd_other (v : α) {j : ℕ} (h : j ≠ i) :
    upd f i v j = f j := by
  ram_all

theorem upd_apply (v : α) (j : ℕ) :
    upd f i v j = if j = i then v else f j := rfl

@[simp] theorem upd_upd_same (v w : α) :
    upd (upd f i v) i w = upd f i w := by
  funext j; by_cases h : j = i <;> ram_all

@[simp] theorem upd_eq_self : upd f i (f i) = f := by
  funext j; by_cases h : j = i <;> ram_all


end

/-- Bound on all entries after an update. -/
theorem upd_le {f : ℕ → ℕ} {W : ℕ} (hf : ∀ j, f j ≤ W) {i v : ℕ} (hv : v ≤ W) (j : ℕ) :
    upd f i v j ≤ W := by
  ram_all <;> ram_grind

/-! ### One lemma per instruction -/

section step
variable {prog : Program} {P : Polygon} {c : Config}

theorem step_jump {l : ℕ} (h : prog[c.pc]? = some (.jump l)) :
    step prog P c = some { c with pc := l } := by
  grind [step]

section
variable {a b l : ℕ} (h : prog[c.pc]? = some (.brLtN a b l))
include l h
theorem step_brLtN_true
    (ht : c.nreg a < c.nreg b) : step prog P c = some { c with pc := l } := by
  grind [step]

theorem step_brLtN_false
    (ht : ¬ c.nreg a < c.nreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  grind [step]


end

section
variable {a b l : ℕ} (h : prog[c.pc]? = some (.brLtR a b l))
include l h
theorem step_brLtR_true
    (ht : c.rreg a < c.rreg b) : step prog P c = some { c with pc := l } := by
  grind [step]

theorem step_brLtR_false
    (ht : ¬ c.rreg a < c.rreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  grind [step]


end

end step

/-! ### `run` -/

section run
variable {prog : Program} {P : Polygon}

@[simp] theorem run_zero (c : Config) : run prog P 0 c = some c := rfl

theorem run_succ (k : ℕ) (c : Config) :
    run prog P (k + 1) c = (step prog P c).bind (run prog P k) := rfl

theorem run_succ_of_step {k : ℕ} {c c₁ : Config} (h : step prog P c = some c₁) :
    run prog P (k + 1) c = run prog P k c₁ := by
  core_grind

/-- Running `a + b` steps is running `a` steps and then `b` steps. -/
theorem run_add (a b : ℕ) (c : Config) :
    run prog P (a + b) c = (run prog P a c).bind (run prog P b) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    simp_all [Nat.succ_add, run_succ, Option.bind_assoc] 

theorem run_add_of_run {a b : ℕ} {c c₁ : Config} (h : run prog P a c = some c₁) :
    run prog P (a + b) c = run prog P b c₁ := by
  grind [run_add, Option.bind_some]

end run

/-! ### Word bounds and `RunsWithin` -/

theorem WordsBounded.mono {W W' : ℕ} {c : Config} (h : WordsBounded W c) (hW : W ≤ W') :
    WordsBounded W' c :=
  by core_grind

@[simp] theorem wordsBounded_setPc {W : ℕ} {c : Config} {p : ℕ} :
    WordsBounded W { c with pc := p } ↔ WordsBounded W c := Iff.rfl

section
variable {W : ℕ} {c : Config} (h : WordsBounded W c)
include h
theorem WordsBounded.nreg (r : ℕ) : c.nreg r ≤ W :=
  h.1 r

/-- Updating a natural register with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nreg {r v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nreg := upd c.nreg r v } :=
  ⟨upd_le h.1 hv, h.2⟩

/-- Updating a natural memory cell with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nmem {a v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nmem := upd c.nmem a v } :=
  ⟨h.1, upd_le h.2 hv⟩

/-! ### Bounded runs

`BoundedRun prog P W k c` says that the `k`-step run from `c` succeeds and every configuration
visited (including the first and the last) is `WordsBounded W`.  `RunsTo` adds the final
configuration.  These compose (`RunsTo.trans`) and give `RunsWithin` directly
(`runsWithin_of_runsTo`). -/


end

section
variable (prog : Program) (P : Polygon) (W k : ℕ)
include prog P W k
/-- The `k`-step run from `c` does not fault and every visited configuration is
`WordsBounded W`. -/
def BoundedRun (c : Config) : Prop :=
  ∀ i, i ≤ k → ∃ c', run prog P i c = some c' ∧ WordsBounded W c'

/-- The `k`-step run from `c` ends in `c'`, and every visited configuration is `WordsBounded W`. -/
def RunsTo (c c' : Config) : Prop :=
  run prog P k c = some c' ∧ BoundedRun prog P W k c


end

section runsTo
variable {prog : Program} {P : Polygon} {W : ℕ}

theorem BoundedRun.wb_start {k : ℕ} {c : Config} (h : BoundedRun prog P W k c) :
    WordsBounded W c := by
  obtain ⟨c', hc, hw⟩ := h 0 (Nat.zero_le _)
  simp_all

theorem BoundedRun.zero {c : Config} (h : WordsBounded W c) : BoundedRun prog P W 0 c := by
  intro i hi
  simp_all

theorem BoundedRun.cons {k : ℕ} {c c₁ : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : BoundedRun prog P W k c₁) :
    BoundedRun prog P W (k + 1) c := by
  intro i hi
  cases i with
  | zero => simp_all
  | succ i =>
    obtain ⟨c', hc, hw'⟩ := h i (Nat.le_of_succ_le_succ hi)
    exact ⟨c', by rw [run_succ_of_step hs, hc], hw'⟩

theorem BoundedRun.add {a b : ℕ} {c c₁ : Config} (h₁ : BoundedRun prog P W a c)
    (hr : run prog P a c = some c₁) (h₂ : BoundedRun prog P W b c₁) :
    BoundedRun prog P W (a + b) c := by
  intro i hi
  by_cases hia : i ≤ a
  · ram_grind
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hia)
    obtain ⟨c', hc, hw⟩ := h₂ d (by omega)
    exact ⟨c', by rw [run_add_of_run hr, hc], hw⟩

section
variable {k : ℕ} {c c' : Config} (h : RunsTo prog P W k c c')
include k c c' h
theorem RunsTo.wb_start :
    WordsBounded W c := h.2.wb_start

theorem RunsTo.wb_end :
    WordsBounded W c' := by
  obtain ⟨c'', hc, hw⟩ := h.2 k le_rfl
  rw [h.1, Option.some.injEq] at hc
  simp_all


end

theorem RunsTo.zero {c : Config} (h : WordsBounded W c) : RunsTo prog P W 0 c c :=
  ⟨rfl, BoundedRun.zero h⟩

/-- Prepend one step. -/
theorem RunsTo.cons {k : ℕ} {c c₁ c' : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : RunsTo prog P W k c₁ c') :
    RunsTo prog P W (k + 1) c c' :=
  ⟨by rw [run_succ_of_step hs, h.1], BoundedRun.cons hw hs h.2⟩

/-- A single step between two bounded configurations. -/
theorem RunsTo.single {c c₁ : Config} (hw : WordsBounded W c) (hw₁ : WordsBounded W c₁)
    (hs : step prog P c = some c₁) : RunsTo prog P W 1 c c₁ :=
  RunsTo.cons hw hs (RunsTo.zero hw₁)

theorem RunsTo.trans {a b : ℕ} {c c₁ c' : Config} (h₁ : RunsTo prog P W a c c₁)
    (h₂ : RunsTo prog P W b c₁ c') : RunsTo prog P W (a + b) c c' :=
  ⟨by rw [run_add_of_run h₁.1, h₂.1], BoundedRun.add h₁.2 h₁.1 h₂.2⟩

/-- Append one step. -/
theorem RunsTo.snoc {k : ℕ} {c c₁ c' : Config} (h : RunsTo prog P W k c c₁)
    (hs : step prog P c₁ = some c') (hw : WordsBounded W c') :
    RunsTo prog P W (k + 1) c c' :=
  h.trans (RunsTo.single h.wb_end hw hs)

/-- Replace the step count by an equal one (for arithmetic normalisation). -/
theorem RunsTo.cast {k k' : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') (hk : k = k') :
    RunsTo prog P W k' c c' := hk ▸ h

/-- `RunsWithin` from a bounded run of `initConfig` ending at a `halt`. -/
theorem runsWithin_of_runsTo {k : ℕ} {c : Config} (h : RunsTo prog P W k initConfig c)
    (hh : AtHalt prog c) : RunsWithin prog P W (k + 1) c.output :=
  ⟨k, le_rfl, h.2, c, h.1, hh, rfl⟩

end runsTo

end

end Machine

namespace Instr

@[expose] public section

/-- Is the instruction a control instruction (`halt`, `jump`, `brLtN`, `brLtR`)? -/
def isControl : Instr → Bool
  | .halt => true
  | .jump _ => true
  | .brLtN _ _ _ => true
  | .brLtR _ _ _ => true
  | _ => false

/-- A straight-line instruction: anything but `halt`, `jump`, `brLtN`, `brLtR`.  Straight-line
instructions always advance the program counter by one and never depend on it. -/
def IsStraight (ins : Instr) : Prop := ins.isControl = false

@[simp] theorem isStraight_halt : ¬ IsStraight .halt := by simp [IsStraight, isControl]
@[simp] theorem isStraight_jump (l : ℕ) : ¬ IsStraight (.jump l) := by simp [IsStraight, isControl]
@[simp] theorem isStraight_brLtN (a b l : ℕ) : ¬ IsStraight (.brLtN a b l) := by
  simp [IsStraight, isControl]
@[simp] theorem isStraight_brLtR (a b l : ℕ) : ¬ IsStraight (.brLtR a b l) := by
  simp [IsStraight, isControl]
@[simp] theorem isStraight_inputSize (r : ℕ) : IsStraight (.inputSize r) := rfl
@[simp] theorem isStraight_constN (r k : ℕ) : IsStraight (.constN r k) := rfl
@[simp] theorem isStraight_copyN (r a : ℕ) : IsStraight (.copyN r a) := rfl
@[simp] theorem isStraight_addN (r a b : ℕ) : IsStraight (.addN r a b) := rfl
@[simp] theorem isStraight_subN (r a b : ℕ) : IsStraight (.subN r a b) := rfl
@[simp] theorem isStraight_loadN (r a : ℕ) : IsStraight (.loadN r a) := rfl
@[simp] theorem isStraight_storeN (a r : ℕ) : IsStraight (.storeN a r) := rfl
@[simp] theorem isStraight_constR (r : ℕ) (z : ℤ) : IsStraight (.constR r z) := rfl
@[simp] theorem isStraight_copyR (r a : ℕ) : IsStraight (.copyR r a) := rfl
section
variable (r a b : ℕ)
@[simp] theorem isStraight_addR : IsStraight (.addR r a b) := rfl
@[simp] theorem isStraight_subR : IsStraight (.subR r a b) := rfl
@[simp] theorem isStraight_mulR : IsStraight (.mulR r a b) := rfl
@[simp] theorem isStraight_divR : IsStraight (.divR r a b) := rfl

end

@[simp] theorem isStraight_loadR (r a : ℕ) : IsStraight (.loadR r a) := rfl
@[simp] theorem isStraight_storeR (a r : ℕ) : IsStraight (.storeR a r) := rfl
@[simp] theorem isStraight_readX (r a : ℕ) : IsStraight (.readX r a) := rfl
@[simp] theorem isStraight_readY (r a : ℕ) : IsStraight (.readY r a) := rfl
@[simp] theorem isStraight_emit (a b d : ℕ) : IsStraight (.emit a b d) := rfl

end

end Instr

namespace Machine

@[expose] public section

/-! ### Frame lemmas

What a single step leaves unchanged, classified by the instruction executed. -/

section frame
variable {prog : Program} {P : Polygon} {c c' : Config} {ins : Instr}

end frame

end

end Machine

end Chazelle
