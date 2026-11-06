module

public import ThreeSumApsp.Lang.Compiler.Simulation
public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.WordSize
public import ThreeSumApsp.Machine.Solving
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Tasks
public import ThreeSumApsp.Util.Flag

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/


open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The number read off the text -/

/-- The number of local variables of every frame: the width of the text, and at least 3 for the
outermost frame. -/
def frameSize (P : Program) : ℕ := max 3 (maxOf Stmt.width P)

/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : Program) : 3 ≤ frameSize P := le_max_left _ _

/-- Every body fits into a frame. -/
theorem width_le_frameSize {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P :=
  (maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)

/-! ## The parts of the code -/

/-- The outermost statement: procedure p0 is called on the local variables 1 and 2 of the outermost
frame, and its result goes to local variable 0. -/
def _root_.Light.mainStmt (p0 : ℕ) : Stmt := .call p0 [.var 1, .var 2] 0

/-- What follows the outermost statement, from position pos on: the result, which is local
variable 0 of the outermost frame, goes to the cell `cRESULT`; then the machine accepts, or, if dec
is set, it accepts if the result is positive and rejects if not. -/
def tailCode (dec : Bool) (pos : ℕ) : List Instr :=
  .add cRESULT (cStack mainFrame) cZERO ::
    (if dec then [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept]
      else [.accept])

/-- The position of the outermost statement: after the four instructions of `headCode`. -/
def mainPos : ℕ := 4

/-- The position of the code that follows the outermost statement. -/
def tailPos (F : ℕ) : ℕ := mainPos + (mainStmt 0).size F

/-- The position of the first body: after the outermost statement and what follows it. -/
def firstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length

/-- The positions of the bodies, the first of them at pos.  A body is followed by the return
sequence. -/
def entries (F : ℕ) : List Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + epilogueSize)

/-- The position after the bodies, the first of them at pos. -/
def endPos (F : ℕ) : List Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + epilogueSize)

/-- The position after the last body, which is the position of the dispatcher.  It is also the
largest number in the pool. -/
def dispPos (P : Program) (dec : Bool) : ℕ := endPos (frameSize P) P (firstBody (frameSize P) dec)

/-- What the code of the statements of P needs to know about the whole code. -/
def codeLayout (P : Program) (dec : Bool) : CodeLayout :=
  ⟨frameSize P, entries (frameSize P) P (firstBody (frameSize P) dec), dispPos P dec⟩

/-- The bodies with their return sequences, the first of them at pos. -/
def bodiesCode (G : CodeLayout) : List Stmt → ℕ → List Instr
  | [], _ => []
  | b :: bs, pos =>
    (compileStmt G b pos ++ epilogue G) ++ bodiesCode G bs (pos + b.size G.F + epilogueSize)

/-- The first three instructions: the numbers 1, 0, -1. -/
def headStraight : List Instr := [.one cONE, .sub cZERO cONE cONE, .sub cNEG cZERO cONE]

/-- The code that fills the pool with the numbers 0, …, N. -/
def poolCode (N : ℕ) : List Instr :=
  .sub (cPool 0) cONE cONE :: (List.range N).map fun n => .add (cPool (n + 1)) (cPool n) cONE

/-- The code that puts zeros into the local variables of the outermost frame. -/
def zeroCode (F : ℕ) : List Instr :=
  (List.range F).map fun x => .sub (cStack (mainFrame + x)) cONE cONE

/-- The code that sets up the outermost frame: FP, zeros in its local variables, and then the two
arguments in its local variables 1 and 2. -/
def frameCode (F : ℕ) : List Instr :=
  .sub cFP cZERO (cPool (2 * mainFrame)) ::
    (zeroCode F ++
      [.add (cStack (mainFrame + 1)) cARG1 cZERO, .add (cStack (mainFrame + 2)) cARG2 cZERO])

/-- The start-up code without its last jump. -/
def startStraight (F N : ℕ) : List Instr := poolCode N ++ frameCode F

/-- The first part: the numbers 1, 0, -1, and the jump to the start-up code. -/
def headCode (P : Program) (dec : Bool) : List Instr :=
  headStraight ++ [.bltz cNEG (3 * dispPos P dec)]

/-- The second part: the outermost statement and the verdict. -/
def mainCode (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  compileStmt (codeLayout P dec) (mainStmt p0) mainPos ++ tailCode dec (tailPos (frameSize P))

/-- The last part: the start-up code and the jump back to the outermost statement. -/
def startCode (P : Program) (dec : Bool) : List Instr :=
  startStraight (frameSize P) (dispPos P dec) ++ [.bltz cNEG mainPos]

/-- **The code of a program.**  With dec = false the machine accepts at the end of the run; with
dec = true it accepts if the result of procedure p0 is positive and rejects if not. -/
def _root_.Light.compileProgram (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  headCode P dec ++ mainCode P p0 dec ++ bodiesCode (codeLayout P dec) P
      (firstBody (frameSize P) dec) ++
    dispatcher (dispPos P dec) ++ startCode P dec

/-! ## Lengths and positions -/

theorem le_endPos (F : ℕ) : ∀ (bs : List Stmt) (pos : ℕ), pos ≤ endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (le_endPos F bs (pos + b.size F + epilogueSize))

/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [mainStmt, Stmt.size, callSize, argsSize, Expr.size]

/-- The outermost statement uses the local variables 0, 1, 2. -/
theorem width_mainStmt (p0 : ℕ) : (mainStmt p0).width = 3 := rfl

theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl

/-- The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
pointer, and it reaches further down than the 2 F + 1 temporaries. -/
theorem two_mul_frameSize_add_le_dispPos (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by
  have : firstBody (frameSize P) dec ≤ dispPos P dec := le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [firstBody, tailPos, mainPos, size_mainStmt, length_tailCode] at this
  omega

theorem length_bodiesCode (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), pos + (bodiesCode G bs pos).length = endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have := length_bodiesCode G bs (pos + b.size G.F + epilogueSize)
    simp only [bodiesCode, endPos, List.length_append, length_compileStmt, length_epilogue]
    omega

section parts

variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem length_through_mainCode :
    (headCode P dec ++ mainCode P p0 dec).length = firstBody (frameSize P) dec := by
  simp only [headCode, headStraight, mainCode, List.length_append, length_compileStmt,
    size_mainStmt, length_tailCode, firstBody, tailPos, mainPos, codeLayout, List.length_cons,
    List.length_nil]
  omega

theorem length_through_bodiesCode :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)).length = dispPos P dec := by
  rw [List.length_append, length_through_mainCode]
  exact length_bodiesCode (codeLayout P dec) P _

theorem length_through_dispatcher :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec) ++
      dispatcher (dispPos P dec)).length = 3 * dispPos P dec := by
  rw [List.length_append, length_through_bodiesCode, length_dispatcher]
  omega

/-- The first part is at position 0. -/
theorem codeAt_headCode : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) :=
  (codeAt_self _).left.left.left.left

theorem codeAt_mainCode : CodeAt (compileProgram P p0 dec) mainPos (mainCode P p0 dec) :=
  (codeAt_self _).left.left.left.right

/-- The outermost statement is at `mainPos`. -/
theorem codeAt_mainStmt :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) :=
  (codeAt_mainCode P p0 dec).left

/-- The code for the verdict follows the outermost statement. -/
theorem codeAt_tailCode :
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) :=
  (codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [length_compileStmt, size_mainStmt, tailPos, codeLayout])

/-- The bodies begin at `firstBody`. -/
theorem codeAt_bodiesCode :
    CodeAt (compileProgram P p0 dec) (firstBody (frameSize P) dec)
      (bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)) :=
  (codeAt_self _).left.left.right.cast_pos (by rw [length_through_mainCode, Nat.zero_add])

/-- The dispatcher is at `dispPos`. -/
theorem codeAt_dispatcher_dispPos :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) :=
  (codeAt_self _).left.right.cast_pos (by rw [length_through_bodiesCode, Nat.zero_add])

/-- The start-up code follows the dispatcher. -/
theorem codeAt_startCode :
    CodeAt (compileProgram P p0 dec) (3 * dispPos P dec) (startCode P dec) :=
  (codeAt_self _).right.cast_pos (by rw [length_through_dispatcher, Nat.zero_add])

end parts

/-- Every body is at its entry, followed by the return sequence, and ends at or before the position
after the bodies. -/
theorem codeAt_bodies {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    codeAt_bodies G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, length_compileStmt, length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/


variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

theorem effects_headStraight (m : ℤ → BitVec W) :
    effects headStraight m =
      Function.update (Function.update (Function.update m cONE (wd W 1)) cZERO (wd W 0)) cNEG
        (wd W (-1)) := by
  simp only [headStraight, effects_cons, effects_nil]
  rw [effect_one, effect_sub cZERO (by cell_read) (by cell_read),
    effect_sub cNEG (by cell_read) (by cell_read)]
  rfl

/-- The three registers after the first three instructions. -/
theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧ effects headStraight m cZERO = wd W 0 ∧
      effects headStraight m cNEG = wd W (-1) := by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> cell_read

/-! ## The pool -/

theorem poolCode_succ (N : ℕ) :
    poolCode (N + 1) = poolCode N ++ [.add (cPool (N + 1)) (cPool N) cONE] := by
  simp [poolCode, List.range_succ]

theorem agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Pool N) m (effects (poolCode N) m) := by
  refine agreeOutside_effects (l := poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show cPool 0 ∈ Pool N
    cells
  · have := List.mem_range.1 hn
    show cPool (n + 1) ∈ Pool N
    cells

/-- After `poolCode N` the pool holds the numbers 0, …, N. -/
theorem effects_poolCode (hone : m cONE = wd W 1) (N : ℕ) :
    ∀ n ≤ N, effects (poolCode N) m (cPool n) = wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [poolCode, List.range_zero, List.map_nil, effects_cons, effects_nil]
    rw [effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [poolCode_succ, effects_append, effects_cons, effects_nil,
      effect_add _ (ih N le_rfl) ((agreeOutside_poolCode N m).read (by cells) hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne (by cells), ih n (by omega)]

/-- The memory after the first three instructions and the code for the pool. -/
def poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (poolCode N) (effects headStraight m)

theorem agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N) m (poolMem N m) := by
  refine AgreeOutside.trans_union ?_ (agreeOutside_poolCode N _)
  rw [effects_headStraight]
  exact (((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
theorem poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    poolMem N m cONE = wd W 1 ∧ poolMem N m cZERO = wd W 0 ∧ poolMem N m cNEG = wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := effects_headStraight_consts m
  have keep := agreeOutside_poolCode N (effects headStraight m)
  exact ⟨keep.read (by cells) one, keep.read (by cells) zero, keep.read (by cells) neg⟩

theorem poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) :
    poolMem N m (cPool n) = wd W n :=
  effects_poolCode (effects_headStraight_consts m).1 N n hn

/-! ## The outermost frame -/

theorem zeroCode_succ (F : ℕ) :
    zeroCode (F + 1) = zeroCode F ++ [.sub (cStack (mainFrame + F)) cONE cONE] := by
  simp [zeroCode, List.range_succ]

/-- The instructions of `zeroCode` write into the outermost frame. -/
theorem writesIn_zeroCode (F : ℕ) : ∀ i ∈ zeroCode F, WritesIn (MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show cStack (mainFrame + x) ∈ MainFrame F
    cells

/-- The local variables of the outermost frame hold zeros. -/
theorem effects_zeroCode (hone : m cONE = wd W 1) (F : ℕ) :
    ∀ x < F, effects (zeroCode F) m (cStack (mainFrame + x)) = wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' := (agreeOutside_effects (writesIn_zeroCode F) m).read (by cells) hone
    rw [zeroCode_succ, effects_append, effects_cons, effects_nil, effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by cells), ih x hlt]

theorem agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    AgreeOutside ({cFP} ∪ MainFrame F) m (effects (frameCode F) m) := by
  refine agreeOutside_effects (l := frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show cStack (mainFrame + 1) ∈ _
    cells
  · -- local variable 2 := the second argument
    show cStack (mainFrame + 2) ∈ _
    cells

/-- The code for the outermost frame: FP, then zeros, then the two arguments. -/
theorem effects_frameCode {i j : ℤ} (hzero : m cZERO = wd W 0)
    (hpool : m (cPool (2 * mainFrame)) = wd W (2 * mainFrame : ℕ)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) (F : ℕ) :
    effects (frameCode F) m =
      Function.update (Function.update
        (effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))))
        (cStack (mainFrame + 1)) (wd W i)) (cStack (mainFrame + 2)) (wd W j) := by
  -- what the last two instructions read has not been written since the beginning
  have read (a : ℤ) (ha : a ∉ MainFrame F) (hfp : a ≠ cFP) :
      effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))) a = m a :=
    ((agreeOutside_effects (writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero := (read cZERO (by cells) (by cells)).trans hzero
  have arg1 := (read cARG1 (by cells) (by cells)).trans hi
  have arg2 := (read cARG2 (by cells) (by cells)).trans hj
  simp only [frameCode, effects_cons, effects_append, effects_nil]
  -- FP := 0 - 2 mainFrame
  rw [effect_sub cFP hzero hpool, show (0 : ℤ) - (2 * mainFrame : ℕ) = cStack mainFrame from rfl]
  -- after the zeros: local variable 1 := the first argument + 0
  rw [effect_add _ arg1 zero, add_zero]
  -- local variable 2 := the second argument + 0
  rw [effect_add _ (by cell_read using arg2) (by cell_read using zero), add_zero]

/-! ## The memory in which the outermost statement starts -/

/-- The memory after the first three instructions and the start-up code. -/
def startMem (F N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (startStraight F N) (effects headStraight m)

theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    startMem F N m = effects (frameCode F) (poolMem N m) := effects_append _ _ _

/-- The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
frame. -/
theorem agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N ∪ ({cFP} ∪ MainFrame F)) m (startMem F N m) :=
  startMem_eq F N m ▸ (agreeOutside_poolMem N m).trans_union (agreeOutside_frameCode h3 _)

/-- After the start-up code the memory represents the state in which the outermost statement
starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
the cells below -2 of the initial memory. -/
theorem rel_startMem (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) := by
  obtain ⟨one, zero, neg⟩ := poolMem_consts Z.disp m
  have keep₁ := agreeOutside_poolMem Z.disp m
  have keep₂ := agreeOutside_frameCode h3 (poolMem Z.disp m)
  have written := effects_frameCode zero (poolMem_pool m hpool) (keep₁.read (by cells) hi)
    (keep₁.read (by cells) hj) Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
      effects (frameCode Z.F) (poolMem Z.disp m) (cStack (mainFrame + x)) = wd W 0 := by
    rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells)]
    exact effects_zeroCode (by cell_read using one) Z.F x hx
  rw [startMem_eq]
  exact {
    one := keep₂.read (by cells) one
    zero := keep₂.read (by cells) zero
    neg := keep₂.read (by cells) neg
    pool := fun n hn => keep₂.read (by cells) (poolMem_pool m hn)
    fp := by
      rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells),
        (agreeOutside_effects (writesIn_zeroCode Z.F) _).cell (by cells), Function.update_self]
    loc := fun x hx => match x with
      | 0 => zeros 0 hx (by omega) (by omega)
      | 1 => by rw [written, Function.update_of_ne (by cells)]; exact Function.update_self ..
      | 2 => by rw [written]; exact Function.update_self ..
      | x + 3 => zeros (x + 3) hx (by omega) (by omega)
    mem := fun a ha => keep₂.read (by cells) (keep₁.read (by cells) (hm a ha)) }

/-! ## The run from the first instruction to the outermost statement -/

theorem straight_headStraight : ∀ i ∈ headStraight, Straight i := by
  simp [headStraight, Straight]

theorem straight_startStraight (F N : ℕ) : ∀ i ∈ startStraight F N, Straight i := by
  simp [startStraight, poolCode, frameCode, zeroCode, Straight, or_imp, forall_and]

theorem length_startStraight (F N : ℕ) : (startStraight F N).length = N + F + 4 := by
  simp +arith [startStraight, poolCode, frameCode, zeroCode]

/-- From the first instruction to the outermost statement. -/
theorem steps_start (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1))
    (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ := by
  have head := codeAt_headCode P p0 dec
  have start := codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := poolMem_consts (dispPos P dec) m
  have neg₁ : startMem (frameSize P) (dispPos P dec) m cNEG = wd W (-1) := by
    rw [startMem_eq, (agreeOutside_frameCode (three_le_frameSize P) _).cell (by cells), neg]
  -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
  refine ((((steps_straight _ 0 m head.left straight_headStraight).trans
    (steps_jump head.right neg₀ hneg)).trans
    (steps_straight _ _ _ start.left (straight_startStraight _ _))).trans
    (steps_jump start.right neg₁ hneg)).cast_count ?_
  rw [length_startStraight, show headStraight.length = 3 from rfl]
  omega

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.
-/


open EndStatement (exec)

/-! ## The verdict -/

/-- The verdict: accept, or, if dec is set, accept exactly if the result is positive. -/
def _root_.Light.verdictOf (dec : Bool) (r : ℤ) : Bool := !dec || decide (0 < r)

/-- What the code that follows the outermost statement leaves, if it starts in the memory m and the
result is r: the machine is about to give the verdict, the cell `cRESULT` holds the result, and only
that cell and the register D have changed. -/
structure Verdict (code : List Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : Cfg W) : Prop where
  verdict : step code cfg = .inr (verdictOf dec r)
  agree : AgreeOutside {cRESULT, cD} m cfg.mem

/-- The code that follows the outermost statement gets there in at most three steps. -/
theorem steps_tail {code : List Instr} {pos : ℕ} {dec : Bool}
    (hcode : CodeAt code pos (tailCode dec pos)) {m : ℤ → BitVec W} {r : ℤ}
    (hres : m (cStack mainFrame) = wd W r) (hzero : m cZERO = wd W 0) (hr : InRange W (-r)) :
    ∃ (n : ℕ) (cfg : Cfg W), n ≤ 3 ∧ Steps code n ⟨pos, m⟩ cfg ∧ Verdict code dec r m cfg := by
  -- the cell for the result := the result
  have copy : Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m cRESULT (wd W r)⟩ :=
    add_zero r ▸ steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    exact ⟨1, _, by omega, copy, step_accept hcode.tail.head,
      (AgreeOutside.refl _ m).update (by simp) _⟩
  | true =>
    have rest : CodeAt code (pos + 1)
      [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept] := hcode.tail
    -- D := 0 - the result; go to accept if D < 0; reject
    have run := (copy.trans (steps_sub rest (by cell_read using hzero)
      (by cell_read using hres))).trans
      (steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep : AgreeOutside {cRESULT, cD} m
        (Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r))) :=
      ((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_accept rest.tail.tail.tail.head).trans (by simp [verdictOf, hpos]), keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_reject rest.tail.tail.head).trans (by simp [verdictOf, hpos]), keep⟩

/-! ## Time and space of the compiled program -/

/-- A bound for the number of steps of the compiled program outside the outermost statement:
`dispPos` + `frameSize` + 9 before it (`steps_start`), at most three after it (`steps_tail`), and
the verdict. -/
def startCost (P : Program) (dec : Bool) : ℕ := dispPos P dec + frameSize P + 13

/-- A bound for the number of steps of the compiled program, for c steps of the light program. -/
def _root_.Light.ramSteps (P : Program) (dec : Bool) (c : ℕ) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) * c

/-- The number of cells of the stack that a run within the limits needs. -/
def stackCells (P : Program) (lim : Limits) : ℕ :=
  mainFrame + (frameSize P + 1) * (lim.depth + 1)

theorem frame_le_stackCells (P : Program) (lim : Limits) :
    mainFrame + frameSize P + 1 ≤ stackCells P lim := by
  have := Nat.le_mul_of_pos_right (frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold stackCells
  omega

/-! ## The setting of the simulation theorem -/

section setting

variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}

/-- The compiled program, with its numbers, satisfies what the simulation theorem assumes once and
for all. -/
def setting (P : Program) (p0 : ℕ) (dec : Bool)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) : Setting W where
  toCodeLayout := codeLayout P dec
  lim := lim
  Q := stackCells P lim
  fits := hfit
  offsets_le := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [codeLayout]
    omega
  P := P
  code := compileProgram P p0 dec
  bodyAt := codeAt_bodies (codeLayout P dec) P _ (codeAt_bodiesCode P p0 dec)
  dispatcherAt := codeAt_dispatcher_dispPos P p0 dec
  width _ hb := width_le_frameSize hb

variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))

/-- The outermost statement is at `mainPos` and runs in the frame `mainFrame`. -/
theorem start_mainStmt {σ : State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : Rel (setting P p0 dec hfit).toSizes σ mainFrame m) :
    Start (setting P p0 dec hfit) 0 (mainStmt p0) σ mainPos mainFrame m where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (frame_le_stackCells P lim)
  codeAt := codeAt_mainStmt P p0 dec
  below := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [size_mainStmt, setting, codeLayout, mainPos]
    omega
  width := (width_mainStmt p0).trans_le (three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [setting, codeLayout, stackCells, Nat.sub_zero, Nat.mul_succ]
    omega

/-- The cells from `lim.space` on are not among those that the
start-up code, the outermost statement or the code for the verdict may change. -/
theorem not_mem_of_far {a : ℤ} (ha : (lim.space : ℤ) ≤ a) :
    a ∉ Constants (dispPos P dec) ∪ ({cFP} ∪ MainFrame (frameSize P)) ∪
      Writable (setting P p0 dec hfit).toSizes mainFrame ∪ {cRESULT, cD} := by
  simp only [Writable, setting, codeLayout]
  cells

end setting

/-! ## The theorem -/

/-- The cells 0, 1, 2, … of the memory m of the machine hold the memory μ of the light language,
and μ holds words. -/
structure Holds (W : ℕ) (lim : Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word

/-- What a run of a compiled program needs in the memory m: the memory μ of the light language, and
the arguments i and j, which are words, in their two cells. -/
structure Input (lim : Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends Holds W lim μ m where
  arg1 : m cARG1 = wd W i
  arg2 : m cARG2 = wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word

/-- **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps. -/
theorem compileProgram_correct {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : State} {c : ℕ} {m : ℤ → BitVec W}
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m
        = some (verdictOf dec (σ'.loc 0), m') ∧ Holds W lim σ'.mem m' := by
  have hF := three_le_frameSize P
  have := two_mul_frameSize_add_le_dispPos P dec
  have hσ : State.Bounded lim ⟨frame [0, i, j], μ⟩ :=
    bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  -- the start-up code
  have run₁ := steps_start P p0 dec (setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := agreeOutside_startMem hF (dispPos P dec) m
  -- the outermost statement
  obtain ⟨m', n, fin⟩ := sim (setting P p0 dec hfit) h mainPos mainFrame _ (start_mainStmt hfit hσ
    (rel_startMem _ hF (by simp only [setting, codeLayout, mainFrame]; omega)
      (fun a _ => hm.rep a) hm.arg1 hm.arg2))
  have : n ≤ stepsPerStep (dispPos P dec) * c := fin.le
  have run₂ := fin.run.cast_pos (p' := tailPos (frameSize P))
    (by simp only [tailPos, size_mainStmt, setting, codeLayout])
  -- the verdict
  obtain ⟨k, cfg, hk, run₃, tail⟩ := steps_tail (codeAt_tailCode P p0 dec)
    (fin.rel.loc 0 (show 0 < frameSize P by omega)) fin.rel.zero
    (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  refine ⟨cfg.mem, exec_mono (c := ⟨0, m⟩) (exec_of_steps run tail.verdict) ?_, ⟨fun a => ?_, hσ'.2⟩⟩
  · simp only [ramSteps, startCost]
    omega
  · by_cases ha : a < lim.space
    · exact tail.agree.read (by cells) (fin.rel.mem a ha)
    · rw [keep.cell (not_mem_of_far hfit (by exact_mod_cast not_lt.1 ha)),
        h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a

end Light.Compiler

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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
theorem fits_of_lt {W : ℕ} {lim : Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : Fits W lim N Q := by
  have : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega

/-- Limits that are polynomial in the parameters fit every admissible word size. -/
theorem fits_of_small {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by
  have := h.word
  have := h.space
  have := h.depth
  set pb := polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, polyBound_mul]
    exact polyBound_le hadm hr (by unfold slopeOf at hb; omega)
  have : textBound P dec * pb < 2 ^ textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have : textBound P dec * pb
      = 32 * pb + 8 * ((frameSize P + 1) * pb) + 2 * (dispPos P dec * pb) := by
    unfold textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have : (frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have : dispPos P dec ≤ dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
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

/-- The constant of the time bounds of a compiled program: the two constants of the time. -/
def timeConst (P : Program) (dec : Bool) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec)

/-- The time of a compiled program. -/
theorem ramSteps_le (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by
  have hstart : startCost P dec ≤ timeConst P dec := by unfold timeConst; omega
  have hsim : stepsPerStep (dispPos P dec) ≤ timeConst P dec := by unfold timeConst; omega
  have : ramSteps P dec c ≤ timeConst P dec * c + timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this

theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
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
    WordRam.Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct h.run hfit (input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.output hfit _)]
  exact h.answer

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/


variable {lim : Limits} {P : Program} {d : ℕ}

/-- Local 2 is multiplied κ times by local 1. -/
def powStmt : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => powStmt κ ;; .set 2 (v 2 *' v 1)

/-- The outermost procedure.  Local 1 is n, the content of cell 0.  At size 0 the result is 0 for a
decision problem and 1 for a problem with an output.  Otherwise local 2 is U = n^κ, local 3 is n²,
and the arguments of the solver are expressions in these three; for a problem with an output the
result of the solver is replaced by 1. -/
def topBody (κ p : ℕ) (args : List Expr) (dec : Bool) : Stmt :=
  .set 1 (M (k 0)) ;;
  Stmt.iteNe (v 1) (k 0)
    (.set 2 (k 1) ;;
    powStmt κ ;;
    .set 3 (v 1 *' v 1) ;;
    .call p args 0 ;;
    (if dec then .skip else .set 0 (k 1)))
    (.set 0 (k (if dec then 0 else 1)))

/-- The loop that is written out κ times turns U = 1 into U = n^κ. -/
theorem pow_spec {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) : ∀ κ : ℕ, ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
    Ends lim P d (powStmt κ) ⟨frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  | 0, _ => Ends.skip (by simp)
  | κ + 1, hw => by
    have hle : ((n ^ κ : ℕ) : ℤ) ≤ ((n ^ (κ + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hn (by omega)
    have hval : ((n ^ κ : ℕ) : ℤ) * n = ((n ^ (κ + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    unfold powStmt
    refine Ends.next (4 * κ) ((pow_spec hn a μ κ (hle.trans hw)).mono le_rfl ?_)
    rintro _ rfl
    -- U := U * n
    refine Ends.setTo ((n ^ (κ + 1) : ℕ) : ℤ) rfl ⟨?_, ?_⟩
    · light_norm
      change |((n ^ κ : ℕ) : ℤ) * n| ≤ lim.word
      rw [hval, abs_of_nonneg (Int.natCast_nonneg _)]
      exact hw
    · exact hval

/-- The arguments n, U and four addresses 1, 1 + n², 1 + 2n², 1 + c n² are safe. -/
theorem safe_fourAddresses {c : ℕ} (hc : c ≤ 4) {n : ℕ} {lim : Limits} {σ : State}
    (h3 : σ.loc 3 = ((n * n : ℕ) : ℤ)) (hw : ((8 * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k c *' v 3], e.Safe lim σ := by
  have hnn : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have : (c : ℤ) * ((n : ℤ) * n) ≤ 4 * ((n : ℤ) * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hnn
  have : (0 : ℤ) ≤ (c : ℤ) * ((n : ℤ) * n) := by positivity
  have : (c : ℤ) ≤ 4 := by exact_mod_cast hc
  push_cast at hw h3
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  simp only [Expr.Safe, Expr.val, Op.eval, h3, true_and, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩,
    ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩,
    by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- The verdict that belongs to the result of a decision procedure. -/
theorem verdictOf_flag (p : Prop) : verdictOf true (ThreeSumApsp.flag p) = true ↔ p := by
  by_cases h : p
  · rw [ThreeSumApsp.flag_of h]
    simp [verdictOf, h]
  · rw [ThreeSumApsp.flag_of_not h]
    simp [verdictOf, h]

/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : EndStatement.Problem} (x : Bounded Q)

/-- Cell 0 holds the size. -/
theorem ofEnd_cell0 (loc : ℕ → ℤ) : (M (k 0)).val ⟨loc, memOf ((ofEnd Q).input x)⟩ = x.n := by
  simp [memOf]

/-- All cells of the input are within the size and the bound. -/
theorem ofEnd_input_le : ∀ a ∈ (ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · rw [abs_of_nonneg (by positivity)]
    push_cast
    omega
  · have := Bounded.abs_le ha
    push_cast
    omega

/-- Cell 0 may be read. -/
theorem safe_cell0 {lim : Limits} {σ : State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) :
    (M (k 0)).Safe lim σ := by
  light_norm
  exact ⟨h0, le_rfl, by omega⟩

end OfEnd

/-! ## Polynomials in the size -/

/-- A polynomial in `n` and `U = n^κ` is a polynomial in `n`. -/
theorem polyBound_pow_le (s k κ n : ℕ) {r : ℕ} (hr : (κ + 1) * k ≤ r) :
    polyBound s k [n, n ^ κ] ≤ 2 ^ (s + k) * (n + 1) ^ r := by
  have hpos : 1 ≤ n + 1 := by omega
  have hU : n ^ κ + 1 ≤ 2 * (n + 1) ^ κ := by
    have h1 : n ^ κ ≤ (n + 1) ^ κ := Nat.pow_le_pow_left (by omega) κ
    have h2 : 1 ≤ (n + 1) ^ κ := Nat.one_le_pow _ _ hpos
    omega
  unfold polyBound
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc 2 ^ s * ((n + 1) * (n ^ κ + 1)) ^ k
      ≤ 2 ^ s * ((n + 1) * (2 * (n + 1) ^ κ)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hU) k)
    _ = 2 ^ (s + k) * (n + 1) ^ ((κ + 1) * k) := by
        rw [show (n + 1) * (2 * (n + 1) ^ κ) = 2 * (n + 1) ^ (κ + 1) by ring, mul_pow, ← pow_mul,
          pow_add]
        ring
    _ ≤ 2 ^ (s + k) * (n + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hr)

/-- What connects a problem in the layout of the end statement with a task. -/
structure Wrap (Q : EndStatement.Problem) (task : Task) (dec : Bool) where
  /-- The input and the output take at most cst (n² + 1) cells. -/
  cst : ℕ := 8
  cst_pos : 1 ≤ cst := by omega
  /-- The arguments of the solver, the free pointer last, as expressions in the locals 1 (n), 2 (U)
  and 3 (n²). -/
  args : List Expr
  /-- The instance of the task. -/
  inst : Bounded Q → task.Inst
  /-- The free pointer: the first cell after the output. -/
  fr : Bounded Q → ℕ
  size_eq : ∀ x : Bounded Q, task.size (inst x) = x.n
  bound_eq : ∀ x : Bounded Q, task.bound (inst x) = x.U
  fr_pos : ∀ x : Bounded Q, 1 ≤ fr x
  fr_le : ∀ x : Bounded Q, fr x ≤ cst * (x.n * x.n + 1)
  /-- The expressions have the values that the solver expects. -/
  vals : ∀ (x : Bounded Q) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → args.map (·.val σ) = task.args (inst x) ++ [(fr x : ℤ)]
  /-- They may be evaluated as soon as the addresses of the input and the output fit in a word. -/
  safe : ∀ (x : Bounded Q) (lim : Limits) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → ((cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ e ∈ args, e.Safe lim σ
  /-- At size 0 it is right to reject, for a decision problem, and to accept, whatever the output
  cells hold, for a problem with an output. -/
  zero : ∀ x : Bounded Q, x.n = 0 → ∀ out, (ofEnd Q).IsAnswer x (!dec) out
  /-- The input meets the precondition of the task. -/
  pre : ∀ x : Bounded Q, 1 ≤ x.n → 1 ≤ x.U →
    task.Pre (inst x) (memOf ((ofEnd Q).input x)) (fr x)
  /-- What the task promises is a right answer. -/
  post : ∀ (x : Bounded Q) r μ', 1 ≤ x.n →
    task.Post (inst x) (memOf ((ofEnd Q).input x)) (fr x) r μ' →
    (ofEnd Q).IsAnswer x (verdictOf dec (if dec then r else 1)) fun i =>
      μ' (((ofEnd Q).input x).length + i)

namespace Wrap

variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}

/-- The steps of the outermost procedure, beside those of the solver. -/
def bodySteps (w : Wrap Q task dec) (κ : ℕ) : ℕ := 4 * κ + (w.args.map Expr.cost).sum + 20

/-- The steps of the outermost procedure and of its call, beside those of the solver. -/
def extra (w : Wrap Q task dec) (κ : ℕ) : ℕ := w.bodySteps κ + 4

/-- The limits of the run on an instance. -/
def limits (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) : Limits :=
  { word := ((need x.n x.U).word + (w.fr x + (need x.n x.U).cells) + w.cst * (x.n * x.n + 1) +
      x.U + x.n + 1 : ℕ)
    space := w.fr x + (need x.n x.U).cells
    depth := (need x.n x.U).depth + 2 }

/-- What the run asks of the limits. -/
structure Room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) (lim : Limits) :
    Prop where
  /-- The addresses of the input and the output fit in a word. -/
  cells : ((w.cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word
  /-- The bound on the numbers, and 1, fit in a word. -/
  bound : ((x.U + 1 : ℕ) : ℤ) ≤ lim.word
  space : 1 ≤ lim.space
  depth : 2 ≤ lim.depth
  /-- The solver, called at depth 2 with the free pointer behind the output, has what it needs. -/
  solver : (need x.n x.U).Ok lim (w.fr x) 2

/-- The limits of the run leave that room. -/
theorem room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) :
    w.Room need x (w.limits need x) := by
  have := w.fr_pos x
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp only [limits] <;> omega

/-- The final state holds a right answer to the instance. -/
abbrev Answered (x : Bounded Q) (dec : Bool) (σ : State) : Prop :=
  (ofEnd Q).IsAnswer x (verdictOf dec (σ.loc 0)) fun i => σ.mem (((ofEnd Q).input x).length + i)

/-- The run of the outermost procedure on an instance of size at least 1. -/
theorem body_ends (w : Wrap Q task dec) {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hsol : Solves task P p Tn need) (κ : ℕ) (x : Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ)
    {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ (Tn x.n x.U + w.bodySteps κ) (Answered x dec) := by
  have hbound := hroom.bound
  have hcells := hroom.cells
  have := hroom.depth
  have : x.n * x.n + 1 ≤ w.cst * (x.n * x.n + 1) := Nat.le_mul_of_pos_left _ w.cst_pos
  have hsquare : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := le_trans (Nat.cast_le.2 (by omega)) hcells
  have hU1 : 1 ≤ x.U := hU ▸ Nat.one_le_pow _ _ hn
  push_cast at hbound hsquare
  unfold topBody bodySteps
  -- n := mem[0]
  refine Ends.setToThen (x.n : ℤ) ?_ ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
  -- if n ≠ 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- U := 1
  light_set 1
  -- U := U * n, κ times
  refine Ends.next (4 * κ) ((pow_spec hn 0 _ κ (by rw [← hU]; omega)).mono le_rfl ?_)
  rintro _ rfl
  rw [← hU]
  -- local 3 := n * n
  light_set (x.n * x.n : ℕ)
  -- result := solver(…)
  refine Ends.callToThen (hsol.meets _ (w.inst x) (w.fr x) (w.pre x hn hU1)
    (by rw [w.size_eq, w.bound_eq]; exact hroom.solver)) ?_
    ⟨w.safe x lim _ rfl rfl rfl hcells, w.vals x _ rfl rfl rfl⟩ (by omega)
    (by rw [w.size_eq, w.bound_eq]; light_time)
  intro r μ' hpost
  rw [w.size_eq, w.bound_eq]
  have hanswer := w.post x r μ' hn hpost
  -- for a problem with an output: result := 1
  cases dec
  · exact Ends.set (by light_norm; omega) (by light_time) (by simpa [Answered] using hanswer)
  · exact Ends.skip (by simpa [Answered] using hanswer)

/-- The run of the outermost procedure on an instance of size 0. -/
theorem body_ends_zero (w : Wrap Q task dec) (P : Program) (p κ : ℕ) (x : Bounded Q) (hn : x.n = 0)
    {need : ℕ → ℕ → Need} {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ 9 (Answered x dec) := by
  have hbound := hroom.bound
  push_cast at hbound
  unfold topBody
  -- n := mem[0]
  refine Ends.setToThen (x.n : ℤ) ?_ ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
  -- if n ≠ 0 … else result := 0 or 1
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [hn]) h)
  have hanswer := w.zero x hn
  cases dec <;>
    exact Ends.set (by simp; omega) (by light_time) (by simpa [Answered, verdictOf] using hanswer _)

/-- The outermost call, from the run of its procedure. -/
theorem ends_of_body (w : Wrap Q task dec) {P : Program} {p κ T : ℕ} (x : Bounded Q)
    {need : ℕ → ℕ → Need}
    (h : Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ T (Answered x dec)) :
    Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 0 (mainStmt P.length)
      ⟨frame [0, 0, 0], memOf ((ofEnd Q).input x)⟩ (T + 4) (Answered x dec) :=
  Ends.call T (by simp) (by simp) (by simp only [limits]; omega)
    (h.mono le_rfl fun _ hσ => by simpa [Answered] using hσ) (by light_time)

/-- The limits are polynomial in the size. -/
theorem small (w : Wrap Q task dec) {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : Bounded Q, x.U = x.n ^ κ → Small s k [x.n] (w.limits need x) := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  obtain ⟨r, hr⟩ : ∃ r, r = (κ + 1) * k + κ + 2 := ⟨_, rfl⟩
  refine ⟨s + k + 5 + Nat.size w.cst, r, fun x hU => ?_⟩
  obtain ⟨hword, hcells, hdepth⟩ := hpoly x.n x.U
  have hpos : 1 ≤ x.n + 1 := by omega
  have hneed := polyBound_pow_le s k κ x.n (r := r) (by omega)
  have hsquare : x.n * x.n + 1 ≤ (x.n + 1) ^ r :=
    (by nlinarith : x.n * x.n + 1 ≤ (x.n + 1) ^ 2).trans (Nat.pow_le_pow_right hpos (by omega))
  have hbound : x.n ^ κ ≤ (x.n + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) κ).trans (Nat.pow_le_pow_right hpos (by omega))
  have : x.n + 1 ≤ (x.n + 1) ^ r := Nat.le_self_pow (by omega) _
  have := w.fr_le x
  rw [← hU] at hneed hbound
  -- `X` bounds the parts that do not come from the solver, `Z ≥ X` those that do
  have hXZ : (x.n + 1) ^ r ≤ 2 ^ (s + k) * (x.n + 1) ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  have hgoal : polyBound (s + k + 5 + Nat.size w.cst) r [x.n] =
      32 * (2 ^ Nat.size w.cst * (2 ^ (s + k) * (x.n + 1) ^ r)) := by
    unfold polyBound
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add 2 (s + k + 5) (Nat.size w.cst), pow_add 2 (s + k) 5]
    ring
  generalize 2 ^ (s + k) * (x.n + 1) ^ r = Z at *
  generalize (x.n + 1) ^ r = X at *
  -- `Y ≥ Z` takes in the constant of the layout
  have : w.cst * (x.n * x.n + 1) ≤ 2 ^ Nat.size w.cst * Z :=
    Nat.mul_le_mul (Nat.lt_size_self w.cst).le (hsquare.trans hXZ)
  have : Z ≤ 2 ^ Nat.size w.cst * Z := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  generalize 2 ^ Nat.size w.cst * Z = Y at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [limits, hgoal] <;> omega

/-- The compiled program is run within these limits: what the interface to the machine asks for. -/
theorem topSolves (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (hsol : Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, ProgramSolves (ofEnd Q) (P ++ [topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by
  obtain ⟨s, k, hsmall⟩ := w.small hpoly κ
  refine ⟨s, k, fun x hU => ?_⟩
  have hinput : ∀ a ∈ (ofEnd Q).input x, |a| ≤ (w.limits need x).word := fun a ha =>
    (ofEnd_input_le x a ha).trans (by simp only [limits]; omega)
  rcases Nat.eq_zero_or_pos x.n with hn | hn
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends_zero P p κ x hn (w.room need x))
    have : (c : ℝ) ≤ w.extra κ := by exact_mod_cast hc.trans (by unfold extra bodySteps; omega)
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_right (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends hsol κ x hn hU (w.room need x))
    have : (c : ℝ) ≤ (Tn x.n x.U : ℝ) + w.extra κ := by
      exact_mod_cast hc.trans (by unfold extra; omega)
    have := hT x.n x.U x.U hn (hU ▸ Nat.one_le_pow _ _ hn) le_rfl
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_left (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩

/-- **If the task is solved in time T, the problem is solved on the word RAM within a constant times
T.** -/
theorem realized (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) : Realized Q T := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  intro κ
  obtain ⟨s, k, htop⟩ := w.topSolves hpoly hsol hT κ
  refine ⟨_, _, (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) * (w.extra κ + 1),
    by positivity, fun x hx bits hadm =>
      let ⟨t, verdict, c, ht, he, ha⟩ :=
        solves_of_programSolves htop (r := 1) (fun x => by simp) x hx bits hadm
      ⟨t, verdict, c, ht.trans ?_, he, ha⟩⟩
  -- `K (T + E) + K ≤ K (E + 1) T + K (E + 1)` for `K, E, T ≥ 0`
  have hT0 : (0 : ℝ) ≤ max (T x.n x.U) 0 := le_max_right _ _
  have hK : (0 : ℝ) ≤ (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) := by positivity
  have hE : (0 : ℝ) ≤ (w.extra κ : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) hT0]

end Wrap

end Light
