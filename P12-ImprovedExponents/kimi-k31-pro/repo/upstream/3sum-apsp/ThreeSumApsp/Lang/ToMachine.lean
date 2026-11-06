/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Compiler.WholeProgram
public import ThreeSumApsp.Lang.WordSize
public import ThreeSumApsp.Machine.Solving
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size

/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light

open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

/-! ## The notion for light programs -/

/-- The limits are at most 2^s ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of the instance. -/
structure Small (s k : ℕ) (params : List ℕ) (lim : Limits) : Prop where
  nonneg : 0 ≤ lim.word
  word : lim.word ≤ (polyBound s k params : ℤ)
  space : lim.space ≤ polyBound s k params
  depth : lim.depth ≤ polyBound s k params

/-- What is asked of the run of procedure p0 on the instance x: within the limits lim it ends in the
state σ' after c steps. -/
structure ProgramSolvesAt (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (x : prob.Inst) (T : ℝ) (lim : Limits) (σ' : State) (c : ℕ) : Prop where
  /-- The run starts on the memory that holds the input of the problem. -/
  run : Exec lim P 0 (mainStmt p0) ⟨frame [0, 0, 0], memOf (prob.input x)⟩ σ' c
  /-- It ends within the time bound. -/
  time : (c : ℝ) ≤ T
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ prob.input x, |v| ≤ lim.word
  /-- The limits are polynomial in the parameters of the instance. -/
  small : Small s k (prob.params x) lim
  /-- The result gives the verdict, and the cells after the input hold the output. -/
  answer : prob.IsAnswer x (verdictOf dec (σ'.loc 0)) fun i => σ'.mem ((prob.input x).length + i)

/-- **A light program solves a problem.**  Procedure p0 of P, called on the memory that holds the
input of the problem, ends within T x steps and within limits that are polynomial in the
parameters; its result gives the verdict (if dec: accept exactly if the result is positive;
otherwise accept), and the cells after the input hold the output. -/
def ProgramSolves (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (σ' : State) (c : ℕ),
    ProgramSolvesAt prob P p0 dec s k x (T x) lim σ' c

/-! ## The word size -/

/-- A number that depends on the compiled program only: times the polynomial bound on the limits,
it exceeds all four numbers that have to fit in a word (`Fits`). -/
def textBound (P : Program) (dec : Bool) : ℕ := 32 + 8 * (frameSize P + 1) + 2 * dispPos P dec

/-- The number of binary digits of that number. -/
def textBoundBits (P : Program) (dec : Bool) : ℕ := Nat.size (textBound P dec)

/-- The slope of the word size for a compiled program: the exponents s and k of the bound
2^s ((p₁ + 1) ⋯ (p_r + 1))^k on the limits, and the bits for the numbers that the compiled code
itself forms (offsets in a frame, positions in the code). -/
def slopeOf (P : Program) (dec : Bool) (s k r : ℕ) : ℕ := textBoundBits P dec + s + k * r + k

/-- The word size fits the limits if the limits, the largest number N of the pool and the number Q
of cells of the stack, with the factors of `Fits`, are below a number B ≤ 2^W. -/
private theorem fits_of_lt {W : ℕ} {lim : Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : Fits W lim N Q := by
  have hB' : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega

/-- Limits that are polynomial in the parameters fit every admissible word size. -/
theorem fits_of_small {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by
  have hword := h.word
  have hspace := h.space
  have hdepth := h.depth
  set pb := polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, polyBound_mul]
    exact polyBound_le hadm hr (by unfold slopeOf at hb; omega)
  have hlt : textBound P dec * pb < 2 ^ textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have htext : textBound P dec * pb
      = 32 * pb + 8 * ((frameSize P + 1) * pb) + 2 * (dispPos P dec * pb) := by
    unfold textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have hstack : (frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have hpool : dispPos P dec ≤ dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
  refine fits_of_lt hB ?_ ?_ ?_ ?_
  · -- 2 (2 word + 2) ≤ 4 pb + 4 ≤ 8 pb
    have : ((8 * pb : ℕ) : ℤ) < ((2 ^ textBoundBits P dec * pb : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 8 * pb < 2 ^ textBoundBits P dec * pb)
    omega
  · -- 2 space ≤ 2 pb
    omega
  · -- 4 (4 + (F + 1) (depth + 1)) ≤ 16 pb + 8 (F + 1) pb
    unfold stackCells mainFrame
    omega
  · -- 2 N ≤ 2 N pb
    omega

/-! ## Time and space -/

/-- The constant of the time and space bounds of a compiled program: the two constants of the time,
and the extent of the negative cells that are in use before any call. -/
def timeConst (P : Program) (dec : Bool) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) + lowCell P dec ⟨0, 0, 0⟩

/-- The time of a compiled program. -/
theorem ramSteps_le (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by
  have hstart : startCost P dec ≤ timeConst P dec := by unfold timeConst; omega
  have hsim : stepsPerStep (dispPos P dec) ≤ timeConst P dec := by unfold timeConst; omega
  have : ramSteps P dec c ≤ timeConst P dec * c + timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this

private theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * T + timeConst P dec :=
  (ramSteps_le P dec c).trans (by gcongr)

/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}

/-- The initial memory holds the input, and zeros in the cells of the two arguments. -/
theorem input_loadWords (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    Input lim (memOf ws) 0 0 (loadWords W ws) where
  rep := loadWords_mem_nat W ws
  bounded := AbsLe.abs_getD_le h0 h
  arg1 := loadWords_mem_neg W ws (by decide)
  arg2 := loadWords_mem_neg W ws (by decide)
  arg1_le := by simpa using h0
  arg2_le := by simpa using h0

/-- Reading the output: a cell of a memory that holds μ, as a signed word. -/
theorem Compiler.Holds.output {c : ℤ → BitVec W} (h : Holds W lim μ c) {N Q : ℕ}
    (hfit : Fits W lim N Q) (off i : ℕ) : WordRam.output c off i = μ (off + i) := by
  rw [WordRam.output, ← Nat.cast_add, h.rep]
  exact toInt_wd (hfit.inRange (h.bounded _))

end run

/-! ## Solvers -/

/-- **The compiled program solves the problem on the word RAM**, within C · T + C steps, C depending
on the compiled program only. -/
theorem solves_of_programSolves {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct h.run hfit (input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.holds.output hfit _)]
  exact h.answer

/-! ## Absorbing the additive constant -/

end Light
