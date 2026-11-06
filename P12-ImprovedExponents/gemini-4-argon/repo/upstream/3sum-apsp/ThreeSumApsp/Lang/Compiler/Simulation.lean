module

public import EndStatement
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Set.Function
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ThreeSumApsp.Lang.Syntax
public import Mathlib.Data.Nat.Digits.Defs
public import ThreeSumApsp.Util.List
public import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/

/-- The integer v is the signed value of a W-bit word. -/
def InRange (W : ℕ) (v : ℤ) : Prop := -(2 : ℤ) ^ W ≤ 2 * v ∧ 2 * v < (2 : ℤ) ^ W

/-- The word of an integer. -/
abbrev wd (W : ℕ) (v : ℤ) : BitVec W := BitVec.ofInt W v

/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : InRange W v) : (wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : wd W w.toInt = w := BitVec.ofInt_toInt

theorem wd_add (a b : ℤ) : wd W a + wd W b = wd W (a + b) := (BitVec.ofInt_add a b).symm

theorem wd_mul (a b : ℤ) : wd W a * wd W b = wd W (a * b) := (BitVec.ofInt_mul a b).symm

theorem wd_sub (a b : ℤ) : wd W a - wd W b = wd W (a - b) := by
  rw [sub_eq_add_neg a b, wd, wd, wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem wd_one : (1 : BitVec W) = wd W 1 := BitVec.eq_of_toNat_eq rfl

/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros. -/
theorem loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by
  simp [loadWords, show ¬ ((a : ℤ) < 0) by omega]

/-- The negative cells of the initial memory hold zeros. -/
theorem loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0) :
    loadWords W ws a = wd W 0 := by
  simp [loadWords, ha]

/-! ## Configurations and single steps -/

/-- A configuration of the machine: the position of the next instruction and the memory. -/
structure Cfg (W : ℕ) where
  pc : ℕ
  mem : ℤ → BitVec W

/-- One step: the next configuration, or the verdict. -/
def step (P : List Instr) (c : Cfg W) : Cfg W ⊕ Bool :=
  let m := c.mem
  let write (i : ℤ) (v : BitVec W) : Cfg W ⊕ Bool :=
    .inl ⟨c.pc + 1, fun x => if x = i then v else m x⟩
  match P.getD c.pc .reject with
  | .one i => write i 1
  | .add i j k => write i (m j + m k)
  | .sub i j k => write i (m j - m k)
  | .mul i j k => write i (m j * m k)
  | .load i j => write i (m (m j).toInt)
  | .store i j => write (m i).toInt (m j)
  | .bltz i l => .inl ⟨if (m i).toInt < 0 then l else c.pc + 1, m⟩
  | .accept => .inr true
  | .reject => .inr false

/-! ## Runs -/

/-- n steps of the machine, none of which gives a verdict, lead from c to c'. -/
def Steps (P : List Instr) : ℕ → Cfg W → Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, step P c = .inl c₁ ∧ Steps P n c₁ c'

theorem Steps.refl (c : Cfg W) : Steps P 0 c c := rfl

theorem Steps.one {c c' : Cfg W} (h : step P c = .inl c') : Steps P 1 c c' := ⟨c', h, rfl⟩

/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : Cfg W} (h₁ : Steps P n c c₁) (h₂ : Steps P k c₁ c₂) :
    Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {n p p' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := hp ▸ h

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n n' : ℕ} {c c' : Cfg W} (h : Steps P n c c') (hn : n = n') :
    Steps P n' c c' := hn ▸ h

/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]

/-- A run that reaches a verdict. -/
theorem exec_of_steps {n : ℕ} {c c' : Cfg W} {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    rw [exec_succ_of_step hs]
    exact ih hr

/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/

/-- The program P has the instructions of the list l from position pos on. -/
def CodeAt (P : List Instr) (pos : ℕ) (l : List Instr) : Prop := l <+: P.drop pos

/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List Instr) : CodeAt l 0 l := List.prefix_refl l

/-- The first part of a piece of code. -/
theorem CodeAt.left {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l :=
  CodeAt.right (l₁ := [i]) h

/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos {pos pos' : ℕ} {l : List Instr} (h : CodeAt P pos l) (hp : pos = pos') :
    CodeAt P pos' l := hp ▸ h

/-! ## Straight-line code -/

/-- The instructions that only change the memory and go on to the next position. -/
def Straight : Instr → Prop
  | .one _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .load _ _ | .store _ _ => True
  | _ => False

/-- What an instruction that only changes the memory does to it. -/
def effect (i : Instr) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  match i with
  | .one i => Function.update m i (wd W 1)
  | .add i j k => Function.update m i (m j + m k)
  | .sub i j k => Function.update m i (m j - m k)
  | .mul i j k => Function.update m i (m j * m k)
  | .load i j => Function.update m i (m (m j).toInt)
  | .store i j => Function.update m (m i).toInt (m j)
  | _ => m

/-- What a list of instructions that only change the memory does to it. -/
def effects (l : List Instr) (m : ℤ → BitVec W) : ℤ → BitVec W := l.foldl (fun m i => effect i m) m

@[simp] theorem effects_nil (m : ℤ → BitVec W) : effects [] m = m := rfl

@[simp] theorem effects_cons (i : Instr) (l : List Instr) (m : ℤ → BitVec W) :
    effects (i :: l) m = effects l (effect i m) := rfl

theorem effects_append (l₁ l₂ : List Instr) (m : ℤ → BitVec W) :
    effects (l₁ ++ l₂) m = effects l₂ (effects l₁ m) := by
  simp [effects, List.foldl_append]

theorem step_straight {c : Cfg W} {i : Instr} (h : P.getD c.pc .reject = i)
    (hi : Straight i) : step P c = .inl ⟨c.pc + 1, effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [Straight] at hi <;> simp only [step, h, effect, write, wd_one]

/-- One instruction that only changes the memory. -/
theorem steps_instr {rest : List Instr} {pos : ℕ} {i : Instr}
    (hcode : CodeAt P pos (i :: rest)) (hi : Straight i) (m : ℤ → BitVec W) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, effect i m⟩ :=
  Steps.one (step_straight hcode.head hi)

/-- A list of instructions that only change the memory. -/
theorem steps_straight (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : CodeAt P pc l)
    (hl : ∀ i ∈ l, Straight i) : Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, step_straight hcode.head hi,
      (ih (pc + 1) (effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

/-- The only constant. -/
theorem effect_one (i : ℤ) : effect (.one i) m = Function.update m i (wd W 1) := rfl

/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.add i j k) m = Function.update m i (wd W (a + b)) := by
  rw [effect, hj, hk, wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by
  rw [effect, hj, hk, wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by
  rw [effect, hj, hk, wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by
  rw [effect, hj, toInt_wd ha]

/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by
  rw [effect, hi, toInt_wd ha]

theorem steps_add {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.add i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a + b))⟩ :=
  effect_add i hj hk ▸ steps_instr hcode trivial m

theorem steps_sub {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.sub i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a - b))⟩ :=
  effect_sub i hj hk ▸ steps_instr hcode trivial m

theorem steps_load {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.load i j :: rest))
    (hj : m j = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  effect_load i hj ha ▸ steps_instr hcode trivial m

theorem steps_store {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.store i j :: rest))
    (hi : m i = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  effect_store j hi ha ▸ steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {rest : List Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine Steps.one ?_
  simp only [step, hcode.head, hc, toInt_wd hv]

/-- A run that ends with a branch on the sign of v, where v is negative if and only if p fails. -/
theorem Steps.branch {n l pos pos' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by
  subst hpos
  by_cases hp : p
  · exact ⟨fun _ => by rwa [if_neg (hv.1 hp)] at h, fun h' => absurd hp h'⟩
  · exact ⟨fun h' => absurd h' hp, fun _ => by rwa [if_pos (not_not.1 (mt hv.2 hp))] at h⟩

theorem step_accept {c : Cfg W} (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by
  simp only [step, h]

theorem step_reject {c : Cfg W} (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by
  simp only [step, h]

/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

/-- The memory m' differs from m only in cells of the set s. -/
def AgreeOutside (s : Set ℤ) (m m' : ℤ → BitVec W) : Prop := Set.EqOn m' m sᶜ

theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside t m₂ m₃) :
    AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)

/-- The instruction writes no cell outside s, whatever the memory holds. -/
def WritesIn (s : Set ℤ) : Instr → Prop
  | .one i | .add i _ _ | .sub i _ _ | .mul i _ _ | .load i _ => i ∈ s
  | .store _ _ => False
  | _ => True

theorem WritesIn.mono {i : Instr} (h : WritesIn s i) (hst : s ⊆ t) : WritesIn t i := by
  cases i <;> first | exact hst h | exact h

theorem agreeOutside_effect {i : Instr} (h : WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effect i m) := by
  cases i <;>
    first | exact (AgreeOutside.refl s m).update h _ | exact AgreeOutside.refl s m | exact h.elim

/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by
  induction l generalizing m with
  | nil => exact AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (agreeOutside_effect hi m).trans (ih hl _)

end framing

end ThreeSumApsp.WordRam

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/


namespace Light.Compiler

open EndStatement (Instr)

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/

/-- The cell from which a whole program takes its first argument. -/
def cARG1 : ℤ := -1
/-- The cell from which a whole program takes its second argument. -/
def cARG2 : ℤ := -2
/-- The cell into which a whole program puts its result. -/
def cRESULT : ℤ := -3
/-- The register that holds 1. -/
def cONE : ℤ := -5
/-- The register that holds 0. -/
def cZERO : ℤ := -7
/-- The register that holds -1; an unconditional jump branches on it. -/
def cNEG : ℤ := -9
/-- The frame pointer FP: the address of local variable 0 of the running procedure. -/
def cFP : ℤ := -11
/-- The register ADDR: the address for the next load or store of a local variable. -/
def cADDR : ℤ := -13
/-- The register RET: the result of the procedure that has just returned. -/
def cRET : ℤ := -15
/-- The register RR: the position to return to, counted down by the dispatcher. -/
def cRR : ℤ := -17
/-- The register NFP: the frame pointer of the procedure that is about to be called. -/
def cNFP : ℤ := -19
/-- The register D: the difference that a test branches on. -/
def cD : ℤ := -21
/-- The temporaries. -/
def cT (k : ℕ) : ℤ := -(23 + 4 * (k : ℤ))
/-- The pool of numbers. -/
def cPool (n : ℕ) : ℤ := -(25 + 4 * (n : ℤ))
/-- The cell number j of the stack. -/
def cStack (j : ℕ) : ℤ := -(2 * (j : ℤ))
/-- The frame of the outermost statement of a whole program: the first whose cells lie beyond the
cells of the arguments and the result. -/
def mainFrame : ℕ := 4

/-! ## Expressions and tests -/

/-- The instruction of the machine for an operation. -/
def _root_.Light.Op.instr : Op → ℤ → ℤ → ℤ → Instr
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- Code that builds in the cell c the number with the given binary digits, least significant digit
first: the number of the higher digits, doubled, plus the lowest digit. -/
def digitsCode (c : ℤ) : List ℕ → List Instr
  | [] => [.sub c c c]
  | d :: L => digitsCode c L ++ [.add c c c] ++ (if d = 0 then [] else [.add c c cONE])

/-- The length of `digitsCode c L`. -/
def digitsLen : List ℕ → ℕ
  | [] => 1
  | d :: L => digitsLen L + 1 + (if d = 0 then 0 else 1)

/-- Code that leaves the value of the expression in the temporary T_k, using only T_k, T_{k+1}, …
and ADDR.  A constant is built from its binary digits, in at most 2 log₂ n + 3 instructions. -/
def compileExpr : Expr → ℕ → List Instr
  | .const n, k => digitsCode (cT k) (Nat.digits 2 n)
  | .var x, k => [.sub cADDR cFP (cPool (2 * x)), .load (cT k) cADDR]
  | .op o a b, k => compileExpr a k ++ compileExpr b (k + 1) ++ [o.instr (cT k) (cT k) (cT (k + 1))]
  | .load a, k => compileExpr a k ++ [.load (cT k) (cT k)]

/-- The length of the code of an expression. -/
def _root_.Light.Expr.size : Expr → ℕ
  | .const n => digitsLen (Nat.digits 2 n)
  | .var _ => 2
  | .op _ a b => a.size + b.size + 1
  | .load a => a.size + 1

/-- Code that goes on to the next position if the test holds and jumps to the position l if it does
not.  Both tests evaluate a into T₀ and b into T₁.  For a < b the code forms D = b - a - 1 and
leaves if D < 0.  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative. -/
def compileCond : Cond → ℕ → List Instr
  | .lt a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++ [.sub cD (cT 1) (cT 0), .sub cD cD cONE, .bltz cD l]
  | .eq a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++
      [.sub cD (cT 0) (cT 1), .bltz cD l, .sub cD cZERO cD, .bltz cD l]

/-- The length of the code of a test. -/
def _root_.Light.Cond.size : Cond → ℕ
  | .lt a b => a.size + b.size + 3
  | .eq a b => a.size + b.size + 4

/-! ## Statements -/

/-- What the code of a statement needs to know about the whole program. -/
structure CodeLayout : Type where
  /-- The number of local variables of every frame. -/
  F : ℕ
  /-- The positions of the procedures. -/
  entry : List ℕ
  /-- The position of the dispatcher. -/
  disp : ℕ

/-- The arguments of a call, evaluated into T_k, T_{k+1}, …. -/
def argsCode : List Expr → ℕ → List Instr
  | [], _ => []
  | e :: es, k => compileExpr e k ++ argsCode es (k + 1)

/-- The length of the code for the arguments of a call. -/
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es

/-- The local variables of the new frame: the first n from the temporaries, the others 0. -/
def frameInit (F n : ℕ) : List Instr :=
  (List.range F).flatMap fun i =>
    [.sub cADDR cNFP (cPool (2 * i)), .store cADDR (if i < n then cT i else cZERO)]

/-- The code of a call between the arguments and the jump to the procedure: the address of the new
frame into NFP, its local variables, the position ret to return to, and FP := NFP. -/
def newFrame (F n ret : ℕ) : List Instr :=
  [.sub cNFP cFP (cPool (2 * (F + 1)))] ++ frameInit F n ++
    [.add cADDR cNFP (cPool 2), .store cADDR (cPool ret), .add cFP cNFP cZERO]

/-- A call up to and including the jump to the procedure; ret is the position after the jump. -/
def callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) : List Instr :=
  argsCode args 0 ++ newFrame G.F args.length ret ++ [.bltz cNEG (G.entry.getD p 0)]

/-- The length of a call up to and including the jump. -/
def callSize (F : ℕ) (args : List Expr) : ℕ := argsSize args + 1 + 2 * F + 4

/-- The length of the code of a statement. -/
def _root_.Light.Stmt.size (F : ℕ) : Stmt → ℕ
  | .skip => 0
  | .set _ e => e.size + 2
  | .store a e => a.size + e.size + 1
  | .seq s t => s.size F + t.size F
  | .ite c s t => c.size + s.size F + 1 + t.size F
  | .while c s => c.size + s.size F + 1
  | .call _ args _ => callSize F args + 2

/-- The code of a statement, for the position pos. -/
def compileStmt (G : CodeLayout) : Stmt → ℕ → List Instr
  | .skip, _ => []
  | .set x e, _ => compileExpr e 0 ++ [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)]
  | .store a e, _ => compileExpr a 0 ++ compileExpr e 1 ++ [.store (cT 0) (cT 1)]
  | .seq s t, pos => compileStmt G s pos ++ compileStmt G t (pos + s.size G.F)
  | .ite c s t, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ++
      compileStmt G t (pos + c.size + s.size G.F + 1)
  | .while c s, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG pos]
  | .call p args x, pos =>
    callCode G p args (pos + callSize G.F args) ++
      [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET]

/-- The return sequence of a procedure: the result (local variable 0) into RET, the position to
return to into RR, the frame of the caller, and the jump to the dispatcher. -/
def epilogue (G : CodeLayout) : List Instr :=
  [.load cRET cFP, .add cADDR cFP (cPool 2), .load cRR cADDR,
    .add cFP cFP (cPool (2 * (G.F + 1))), .bltz cNEG G.disp]

/-- The length of the return sequence. -/
def epilogueSize : ℕ := 5

/-- The dispatcher for the positions below n. -/
def dispatcher (n : ℕ) : List Instr :=
  (List.range n).flatMap fun j => [.sub cRR cRR cONE, .bltz cRR j]

/-! ## Lengths -/

theorem length_digitsCode (c : ℤ) (L : List ℕ) : (digitsCode c L).length = digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [digitsCode, digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl

/-- The code of an expression has the length defined on the text. -/
theorem length_compileExpr (e : Expr) (k : ℕ) : (compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [compileExpr, Expr.size, iha, ihb]
  | load a ih => simp [compileExpr, Expr.size, ih]

/-- The code of a test has the length defined on the text. -/
theorem length_compileCond (c : Cond) (l : ℕ) : (compileCond c l).length = c.size := by
  cases c <;> simp +arith [compileCond, Cond.size, length_compileExpr]

/-- The code for the arguments of a call has the length defined on the text. -/
theorem length_argsCode (es : List Expr) (k : ℕ) : (argsCode es k).length = argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [argsCode, argsSize, length_compileExpr, ih]

/-- Two instructions for each local variable of the new frame. -/
theorem length_frameInit (F n : ℕ) : (frameInit F n).length = 2 * F := by
  simp [frameInit, List.length_flatMap, Nat.mul_comm]

/-- The code between the arguments and the jump has 2 F + 4 instructions. -/
theorem length_newFrame (F n ret : ℕ) : (newFrame F n ret).length = 2 * F + 4 := by
  simp +arith [newFrame, length_frameInit]

/-- A call up to its jump has the length defined on the text. -/
theorem length_callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) :
    (callCode G p args ret).length = callSize G.F args := by
  simp +arith [callCode, callSize, length_argsCode, length_newFrame]

theorem length_epilogue (G : CodeLayout) : (epilogue G).length = epilogueSize := rfl

/-- The code of a statement has the length defined on the text. -/
theorem length_compileStmt (G : CodeLayout) (s : Stmt) (pos : ℕ) :
    (compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [compileStmt, Stmt.size, length_compileExpr]
  | store a e => simp +arith [compileStmt, Stmt.size, length_compileExpr]
  | seq s t ihs iht => simp [compileStmt, Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [compileStmt, Stmt.size, ihs, iht, length_compileCond]
  | «while» c s ih => simp +arith [compileStmt, Stmt.size, ih, length_compileCond]
  | call p args x => simp [compileStmt, Stmt.size, length_callCode]

end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/

/-- One more than the largest variable of an expression. -/
def Expr.vars : Expr → ℕ
  | .const _ => 0
  | .var x => x + 1
  | .op _ a b => max a.vars b.vars
  | .load a => a.vars

/-- The number of temporaries that the code of an expression uses. -/
def Expr.height : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => max a.height (b.height + 1)
  | .load a => a.height

/-- The width of an expression: at least its variables and its temporaries. -/
def Expr.width (e : Expr) : ℕ := max e.vars e.height

/-- The width of a test: that of its two sides. -/
def Cond.width : Cond → ℕ
  | .lt a b => max a.width b.width
  | .eq a b => max a.width b.width

/-- The largest value of f on a list. -/
def maxOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: l => max (f x) (maxOf f l)

/-- The width of a statement: at least the width of its expressions, one more than each variable
that it writes, and the number of arguments of each of its calls. -/
def Stmt.width : Stmt → ℕ
  | .skip => 0
  | .set x e => max (x + 1) e.width
  | .store a e => max a.width e.width
  | .seq s t => max s.width t.width
  | .ite c s t => max c.width (max s.width t.width)
  | .while c s => max c.width s.width
  | .call _ args x => max (x + 1) (max args.length (maxOf Expr.width args))

section width

variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem maxOf_le_iff {α : Type} {f : α → ℕ} {l : List α} : maxOf f l ≤ F ↔ ∀ y ∈ l, f y ≤ F := by
  induction l <;> simp [maxOf, *]

theorem Expr.vars_op_le_iff : (Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

theorem Cond.width_lt_le_iff : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Cond.width_eq_le_iff : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Stmt.width_set_le_iff : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff

theorem Stmt.width_store_le_iff : (Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff

theorem Stmt.width_seq_le_iff : (Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff

theorem Stmt.width_ite_le_iff :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [Stmt.width, max_le_iff]

theorem Stmt.width_while_le_iff : (Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff

theorem Stmt.width_call_le_iff :
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [Stmt.width, max_le_iff, maxOf_le_iff, Nat.succ_le_iff]

end width

end Light

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/


open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The numbers that never change -/

/-- The word size is large enough for the limits: words hold 2 · word + 2 (so the difference of two
values, and one less, is in range), all addresses of the memory, all addresses of a stack of Q
cells, and all numbers 0, …, N of the pool. -/
structure Fits (W : ℕ) (lim : Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W

/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v :=
  inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h

/-- The numbers on which the proofs about compiled code depend: the layout of the code, the limits
on the runs of the light program, and the number of stack cells.  The pool holds the numbers from 0
to the position of the dispatcher. -/
structure Sizes (W : ℕ) extends CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp

/-! ## Sets of cells -/

/-- What the evaluation of an expression into T_k may change: ADDR and the temporaries T_j with
k ≤ j ≤ 2 F. -/
def Temps (k F : ℕ) : Set ℤ := {a | a = cADDR ∨ ∃ j, k ≤ j ∧ j ≤ 2 * F ∧ a = cT j}

/-- The stack cells j with q ≤ j < Q. -/
def Stack (q Q : ℕ) : Set ℤ := {a | ∃ j, q ≤ j ∧ j < Q ∧ a = cStack j}

/-- The cells of the local variables of the outermost frame. -/
def MainFrame (F : ℕ) : Set ℤ := Stack mainFrame (mainFrame + F)

/-- The cells of the pool that hold the numbers 0, …, N. -/
def Pool (N : ℕ) : Set ℤ := {a | ∃ n, n ≤ N ∧ a = cPool n}

/-- The cells that the start-up code fills and no compiled statement changes: the registers for 1,
0, -1 and the pool. -/
def Constants (N : ℕ) : Set ℤ := {cONE, cZERO, cNEG} ∪ Pool N

/-- The cells that compiled code uses freely: the registers D, RET, RR, NFP, ADDR and the
temporaries. -/
def Scratch (F : ℕ) : Set ℤ := {cD, cRET, cRR, cNFP} ∪ Temps 0 F

/-- What the code of a statement that runs in the frame q may change: scratch cells, FP, the stack
cells from q on, and the memory cells within the limits. -/
def Writable {W : ℕ} (Z : Sizes W) (q : ℕ) : Set ℤ :=
  Scratch Z.F ∪ {cFP} ∪ Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}

/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/

theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ Temps k F ↔ a = cADDR ∨ cT (2 * F) ≤ a ∧ a ≤ cT k ∧ 4 ∣ cT 0 - a := by
  simp only [Temps, cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega

theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ Stack q Q ↔ cStack Q < a ∧ a ≤ cStack q ∧ 2 ∣ a := by
  simp only [Stack, cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega

theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ Pool N ↔ cPool N ≤ a ∧ a ≤ cPool 0 ∧ 4 ∣ cPool 0 - a := by
  simp only [Pool, cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega

/-- Proves that two cells of the compiled code are different, that a cell is or is not in one of the
sets above, or that one of these sets lies in another or in its complement.  A cell is given by its
name (cFP, cT j, cStack j, …) or is an integer that the context bounds.  The names and the sets are
replaced by their definitions; what remains are inequalities between integers, which follow from
those of the context, such as 1 ≤ q. -/
macro "cells" : tactic =>
  `(tactic| (simp only [Set.subset_def, Set.mem_compl_iff, Constants, Scratch, Writable, MainFrame,
               Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
               mem_temps_iff, mem_stack_iff, mem_pool_iff, cARG1, cARG2, cRESULT, cONE, cZERO, cNEG,
               cFP, cADDR, cRET, cRR, cNFP, cD, cT, cPool, cStack, mainFrame, ne_eq, true_or,
               or_true, false_or, or_false] <;>
             intros <;> omega))

/-- Reads a cell of a memory that is given by writes: it goes through the writes from the last to
the first, until it meets a write to the cell itself or no write is left. -/
macro "cell_read" : tactic =>
  `(tactic| repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by cells)]))

/-- Reads a cell of a memory that is given by writes to other cells of a memory in which, by h, the
cell holds the number in question. -/
macro "cell_read" " using " h:term : tactic => `(tactic| (cell_read; exact $h))

variable {W : ℕ} {Z : Sizes W} {F : ℕ}

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : Temps k F ⊆ Scratch F := by cells

/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : Scratch Z.F ⊆ Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

/-- A statement may change the stack from its frame on. -/
theorem stack_subset_writable {q : ℕ} : Stack q Z.Q ⊆ Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left

/-- A statement in a later frame may change less. -/
theorem writable_subset_writable {q q' : ℕ} (h : q ≤ q') : Writable Z q' ⊆ Writable Z q :=
  Set.union_subset_union_left _ (Set.union_subset_union_right _ (by cells))

/-- A statement may change the memory cells within the limits. -/
theorem mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q :=
  Set.mem_union_right _ h

/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by
  simp only [cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by
  simp only [cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := cStack_add q 1

/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by
  have : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]

/-- The number -1, on which every jump branches, fits in a word. -/
theorem Sizes.inRange_neg_one (Z : Sizes W) : InRange W (-1) := by
  have : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]

/-! ## The relation between a state of the light language and a memory of the machine -/

/-- The memory m of the machine represents the state σ of a procedure whose frame is at q. -/
structure Rel (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m cONE = wd W 1
  zero : m cZERO = wd W 0
  neg : m cNEG = wd W (-1)
  pool : ∀ n ≤ Z.disp, m (cPool n) = wd W n
  fp : m cFP = wd W (cStack q)
  loc : ∀ x < Z.F, m (cStack (q + x)) = wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = wd W (σ.mem a)

section Rel

variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m')
    (hs : s ⊆ (Constants Z.disp)ᶜ) (hfp : m' cFP = wd W (cStack q'))
    (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by cells)).trans R.one
    zero := (keep (by cells)).trans R.zero
    neg := (keep (by cells)).trans R.neg
    pool := fun n hn => (keep (by cells)).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : Rel Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- A memory that differs only in scratch cells and in the stack beyond the frame represents the
same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.) -/
theorem Rel.beyond (R : Rel Z σ q m) (hq : 1 ≤ q)
    (A : AgreeOutside (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- Writing a local variable. -/
theorem Rel.setLoc (R : Rel Z σ q m) (hq : 1 ≤ q) (x : ℕ) (v : ℤ) :
    Rel Z { σ with loc := Function.update σ.loc x v } q
      (Function.update m (cStack (q + x)) (wd W v)) := by
  refine R.of_agreeOutside ((AgreeOutside.refl {cStack (q + x)} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun y hy => ?_) fun a ha => by cell_read using R.mem a ha
  obtain rfl | hxy := eq_or_ne y x
  · simp
  · rw [Function.update_of_ne (by cells)]
    exact (R.loc y hy).trans (by simp [hxy])

/-- Writing a memory cell. -/
theorem Rel.setMem (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  have hnonneg : 0 ≤ a := ha.1
  refine R.of_agreeOutside ((AgreeOutside.refl {a} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun x hx => by cell_read using R.loc x hx) fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · simp [Int.toNat_of_nonneg hnonneg]
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])

/-- Reading a memory cell. -/
theorem Rel.read (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this

/-- The cell to which FP points is local variable 0. -/
theorem Rel.loc_zero (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) :=
  R.loc 0 hF

end Rel

/-- The memory m represents the state σ in the frame q, and the frame lies within the stack: after
stack cell 0 and before stack cell Q. -/
structure Framed (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q

/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩

/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using steps_bltz hcode hneg hr

/-- The two instructions that put the content v of the cell c into the local variable x. -/
theorem steps_setVar {x : ℕ} {c v : ℤ} (I : Framed Z σ q m) (hx : x < Z.F)
    (hcode : CodeAt code pos (.sub cADDR cFP (cPool (2 * x)) :: .store cADDR c :: rest))
    (hc : m c = wd W v) (hne : c ≠ cADDR) :
    ∃ m', Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      AgreeOutside (Writable Z q) m m' := by
  have := Z.offsets_le
  have := I.high
  -- ADDR := FP - 2 x
  have run₁ := steps_sub (i := cADDR) hcode I.rel.fp (I.rel.pool (2 * x) (by omega))
  rw [cStack_sub] at run₁
  have A₁ := (AgreeOutside.refl (Scratch Z.F) m).update (a := cADDR) (by cells)
    (wd W (cStack (q + x)))
  -- the cell at ADDR := c
  have run₂ := run₁.trans (steps_store hcode.tail (Function.update_self _ _ _)
    (Z.inRange_stack (by omega)))
  rw [Function.update_of_ne hne, hc] at run₂
  exact ⟨_, run₂, (I.rel.same A₁).setLoc I.low x v,
    (A₁.mono scratch_subset_writable).update (by cells) _⟩

end code




open EndStatement (Instr)

variable {W : ℕ} {code : List Instr} {disp n : ℕ}

/-- The dispatcher for one more position. -/
theorem dispatcher_succ (n : ℕ) :
    dispatcher (n + 1) = dispatcher n ++ [.sub cRR cRR cONE, .bltz cRR n] := by
  simp [dispatcher, List.range_succ, List.flatMap_append]

/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (dispatcher n).length = 2 * n := by
  simp [dispatcher, List.length_flatMap, Nat.mul_comm]

/-- A shorter dispatcher is the beginning of a longer one. -/
theorem dispatcher_prefix {j n : ℕ} (h : j ≤ n) : dispatcher j <+: dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (dispatcher_succ n ▸ List.prefix_append _ _)

/-- The two instructions for the position j. -/
theorem codeAt_dispatcher {j : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) :
    CodeAt code (disp + 2 * j) [.sub cRR cRR cONE, .bltz cRR j] := by
  have upToPairCode : CodeAt code disp (dispatcher j ++ [.sub cRR cRR cONE, .bltz cRR j]) :=
    dispatcher_succ j ▸ (dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [length_dispatcher])

/-- The two instructions for the position j, when RR holds v: RR goes down by one, and the machine
goes to j if that is negative and to the next pair if not. -/
theorem steps_dispatcher_pair {j : ℕ} (hcode : CodeAt code disp (dispatcher n))
    (hj : j < n) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) {v : ℤ} (hv : InRange W (v - 1)) :
    Steps code 2 ⟨disp + 2 * j, Function.update m cRR (wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m cRR (wd W (v - 1))⟩ := by
  have pairCode := codeAt_dispatcher hcode hj
  -- RR := RR - 1
  have run₁ := steps_sub pairCode (Function.update_self cRR (wd W v) m)
    (by cell_read using hone)
  rw [Function.update_idem] at run₁
  -- if RR < 0 go to j
  exact run₁.trans (steps_bltz pairCode.tail (Function.update_self _ _ _) hv)

/-- The dispatcher from its j-th pair of instructions on, when RR holds k: it arrives at position
j + k.  The positions fit in a word (hn). -/
theorem steps_dispatcher_from (hcode : CodeAt code disp (dispatcher n))
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (k j : ℕ)
    (hjk : j + k < n) :
    Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m cRR (wd W k)⟩
      ⟨j + k, Function.update m cRR (wd W (-1))⟩ := by
  induction k generalizing j with
  | zero =>
    simpa using steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0)
      (by constructor <;> omega)
  | succ k ih =>
    have run := steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1)
      (by constructor <;> omega)
    rw [if_neg (by omega), add_sub_cancel_right] at run
    rw [Nat.cast_succ]
    -- 2 + 2 (k + 1) steps lead to the position j + 1 + k
    exact ((run.trans (ih (j + 1) (by omega))).cast_count (by ring)).cast_pos (by ring)

/-- From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
word (hn). -/
theorem steps_dispatcher {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1)
    (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ := by
  have := steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.mul_zero, Nat.add_zero, Nat.zero_add, ← hRR, Function.update_eq_self] at this

end Light.Compiler

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Writing a bounded number into a bounded function. -/
theorem abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]

/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by
  refine bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact Expr.abs_val_le hσ e (ha e he)

/-- A run that starts with words in all variables and cells ends with words in all of them. -/
theorem Exec.bounded {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨abs_update_le hσ.1 (Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, abs_update_le hσ.2 (Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (bounded_callFrame hσ _ ha)
    exact ⟨abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩

/-- A run does not change the cells from lim.space on. -/
theorem Exec.mem_outside {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by
  induction h with
  | skip => rfl
  | set _ => rfl
  | store _ _ haddr =>
    obtain ⟨h0, hlt⟩ := haddr
    exact Function.update_of_ne (by omega) _ _
  | seq _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | call _ _ _ _ ih => exact ih

end Light

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.
-/



namespace Light.Compiler

variable {W : ℕ} {F : ℕ}

/-- Every expression uses at least one temporary. -/
theorem _root_.Light.Expr.height_pos (e : Expr) : 0 < e.height := by
  induction e with
  | const n => simp [Expr.height]
  | var x => simp [Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
theorem cT_mem_temps_of_height (e : Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    cT k ∈ Temps k F := by
  have := e.height_pos
  cells

/-! ## Constants -/

theorem straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ digitsCode c L, Straight i
  | [] => by simp [digitsCode, Straight]
  | d :: L => by
    have := straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [digitsCode, hd, Straight, or_imp, forall_and] using this

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
theorem effects_digitsCode {c : ℤ} (hc : cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) :
    effects (digitsCode c L) m c = wd W (Nat.ofDigits 2 L : ℕ) ∧
      AgreeOutside {c} m (effects (digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [digitsCode, effects_cons, effects_nil,
      effect_sub c (wd_toInt (m c)).symm (wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [digitsCode, effects_append, effects_append, effects_cons, effects_nil, effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, effects_cons, effects_nil, effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring

/-! ## Expressions -/

theorem straight_instr (o : Op) (i j k : ℤ) : Straight (o.instr i j k) := by
  cases o <;> trivial

/-- The code of an expression only changes the memory. -/
theorem straight_compileExpr : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  | .const _, _ => straight_digitsCode _ _
  | .var _, _ => by simp [compileExpr, Straight]
  | .op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨straight_compileExpr a k, straight_compileExpr b (k + 1)⟩, by simp [straight_instr]⟩
  | .load a, k => List.forall_mem_append.2 ⟨straight_compileExpr a k, by simp [Straight]⟩

/-- The instruction of an operation, on cells that hold known numbers. -/
theorem effect_instr (o : Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = wd W a)
    (hk : m k = wd W b) : effect (o.instr i j k) m = Function.update m i (wd W (o.eval a b)) := by
  cases o
  exacts [effect_add i hj hk, effect_sub i hj hk, effect_mul i hj hk]

variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
theorem effects_compileExpr (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := effects_digitsCode (c := cT k) (by cells) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [compileExpr, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), cStack_sub,
      effect_load (cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((AgreeOutside.refl _ m).update (by cells) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by cells), I.rel.loc x hx, Expr.val]
  | op o a b iha ihb =>
    have hk := cT_mem_temps_of_height _ hT
    have : a.height ≤ (Expr.op o a b).height := le_max_left _ _
    have : b.height + 1 ≤ (Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [compileExpr, effects_append, effects_append, effects_cons, effects_nil,
      effect_instr o (cT k) (Ab.read (by cells) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by cells))).update hk _⟩
  | load a ih =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [compileExpr, effects_append, effects_cons, effects_nil,
      effect_load (cT k) va (Z.inRange_addr haddr), Aa.cell (by cells), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩

/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  effects_compileExpr I e k (Expr.width_le_iff.1 hw).1 hs
    (by have := (Expr.width_le_iff.1 hw).2; omega)


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).
-/




open EndStatement (Instr)

variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

/-! ## Two expressions -/

/-- What follows the code of two expressions. -/
theorem codeAt_after_pair (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, length_compileExpr, length_compileExpr])

/-- The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
scratch cells only. -/
theorem steps_pair (I : Framed Z σ q m)
    (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧
      AgreeOutside (Scratch Z.F) m m' := by
  obtain ⟨va, Aa⟩ := effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have := Aa.mono temps_subset_scratch
  obtain ⟨vb, Ab⟩ := effects_compileExpr_of_width (I.same this) b 1 hwb hsb (by omega)
  have run := steps_straight _ pos m hcode.left
    (List.forall_mem_append.2 ⟨straight_compileExpr a 0, straight_compileExpr b 1⟩)
  rw [List.length_append, length_compileExpr, length_compileExpr, effects_append] at run
  exact ⟨_, run, Ab.read (by cells) va, vb, this.trans (Ab.mono temps_subset_scratch)⟩

/-! ## Tests -/

/-- What the code of a test does, if it has size instructions, begins at pos, and tests p: in at
most size steps the machine reaches the position after the code if p holds, and the position l if
not.  Only scratch cells change. -/
def Decides (code : List Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
    (p → Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → Steps code n ⟨pos, m⟩ ⟨l, m'⟩)

/-- The test holds. -/
theorem Decides.of_holds {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- The test fails. -/
theorem Decides.of_fails {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : ¬ p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨l, m'⟩ :=
  let ⟨m', n, le, A, _, run⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- No overflow: the difference of two values fits in a word, and so does one less. -/
theorem inRange_sub (Z : Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word)
    (hy : |y| ≤ Z.lim.word) : InRange W (x - y) ∧ InRange W (x - y - 1) := by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]

/-- The test a < b. -/
theorem decides_lt (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.lt a b) l)) (hw : (Cond.lt a b).width ≤ Z.F)
    (hs : (Cond.lt a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.lt a b).size l m (a.val σ < b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := b - a
  have run₂ := run₁.trans (steps_sub restCode vb va)
  -- D := D - 1
  have run₃ := run₂.trans (steps_sub restCode.tail (Function.update_self _ _ _)
    (by cell_read using (I.rel.same A₁).one))
  -- leave if D < 0
  have run₄ := run₃.trans (steps_bltz restCode.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z (Expr.abs_val_le hσ b hsb) (Expr.abs_val_le hσ a hsa)).2)
  exact ⟨_, _, by rw [Cond.size], (A₁.update (by cells) _).update (by cells) _,
    run₄.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The test a = b. -/
theorem decides_eq (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.eq a b) l)) (hw : (Cond.eq a b).width ≤ Z.F)
    (hs : (Cond.eq a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.eq a b).size l m (a.val σ = b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := Expr.abs_val_le hσ a hsa
  have hb := Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := a - b
  have run₂ := run₁.trans (steps_sub restCode va vb)
  have A₂ := A₁.update (a := cD) (by cells) (wd W (a.val σ - b.val σ))
  -- leave if D < 0
  have run₃ := run₂.trans (steps_bltz restCode.tail (Function.update_self _ _ _)
    (inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  -- D := 0 - D
  have run₄ := run₃.trans (steps_sub restCode.tail.tail
    (by cell_read using (I.rel.same A₁).zero)
    (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  -- leave if D < 0
  have run₅ := run₄.trans (steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z hb ha).1)
  exact ⟨_, _, by rw [Cond.size], A₂.update (by cells) _,
    run₅.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The code of a test decides the test. -/
theorem decides_compileCond (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact decides_lt I hσ hcode hw hs
  | eq a b => exact decides_eq I hσ hcode hw hs


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.
-/




variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/

/-- The code of the arguments only changes the memory. -/
theorem straight_argsCode : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  | [], _ => by simp [argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨straight_compileExpr e k, straight_argsCode es (k + 1)⟩

/-- The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
and the temporaries from T_k on. -/
theorem effects_argsCode (I : Framed Z σ q m) (es : List Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) := by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [argsCode, effects_append]
    refine ⟨fun i hi => ?_, Ae.trans (Aes.mono (by cells))⟩
    cases i with
    | zero => exact Aes.read (by cells) ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)

/-! ## The new frame -/

/-- The code for one more local variable. -/
theorem frameInit_succ (F' n : ℕ) : frameInit (F' + 1) n = frameInit F' n ++
    [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] := by
  simp [frameInit, List.range_succ, List.flatMap_append]

theorem straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ frameInit F' n, Straight i
  | 0 => by simp [frameInit]
  | F' + 1 => by
    rw [frameInit_succ]
    exact List.forall_mem_append.2 ⟨straight_frameInit n F', by simp [Straight]⟩

/-- The code that fills the first F' local variables of the new frame at q': the first n from the
temporaries, the others with 0.  It changes nothing but ADDR and stack cells from q' on. -/
theorem effects_frameInit (Z : Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W)
    (hNFP : m cNFP = wd W (cStack q'))
    (hpool : ∀ i < F', m (cPool (2 * i)) = wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F',
        effects (frameInit F' n) m (cStack (q' + i)) = if i < n then m (cT i) else m cZERO) ∧
      AgreeOutside (insert cADDR (Stack q' Z.Q)) m (effects (frameInit F' n) m) := by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), AgreeOutside.refl _ m⟩
  | succ F' ih =>
    obtain ⟨val, A⟩ := ih (fun i hi => hpool i (by omega)) (by omega)
    -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
    rw [frameInit_succ, effects_append, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR (A.read (by cells) hNFP) (A.read (by cells) (hpool F' (by omega))),
      cStack_sub, effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨fun i hi => ?_, (A.update (by cells) _).update (by cells) _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)]
    · cell_read using val i (by omega)

/-- The code of the new frame only changes the memory. -/
theorem straight_newFrame (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [Straight], straight_frameInit n F⟩,
    by simp [Straight]⟩

/-- The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
before that frame holds the position to return to.  Of the stack, only cells from q + F on have
changed. -/
theorem effects_newFrame (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
      AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) := by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [newFrame, effects_append, effects_cons, effects_nil]
  -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
  -- frame q change, so the memory goes on representing σ in the frame q.
  rw [effect_sub cNFP R.fp (R.pool _ hN), cStack_sub, ← Nat.add_assoc]
  have A₁ := (AgreeOutside.refl (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m).update (a := cNFP) (by cells)
    (wd W (cStack (q + Z.F + 1)))
  -- the local variables of the new frame
  obtain ⟨val, A⟩ := effects_frameInit Z args.length (q + Z.F + 1) Z.F _
    (Function.update_self cNFP _ m) (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize effects (frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ cNFP = wd W (cStack (q + Z.F + 1)) :=
    A.read (by cells) (Function.update_self _ _ _)
  have A₂ := A₁.trans (A.mono (by cells))
  -- ADDR := NFP + 2
  rw [effect_add cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), cStack_succ_add]
  have A₃ := A₂.update (a := cADDR) (by cells) (wd W (cStack (q + Z.F)))
  -- the cell at ADDR := ret
  rw [effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)),
    (R.beyond hq A₃).pool ret hret]
  have A₄ := A₃.update (a := cStack (q + Z.F)) (by cells) (wd W ret)
  have R₄ := R.beyond hq A₄
  -- FP := NFP + 0
  rw [effect_add cFP (by cell_read using hNFP) R₄.zero, add_zero]
  refine ⟨?_, by cell_read,
    (A₄.mono (Set.union_subset scratch_subset_writable stack_subset_writable)).update (by cells) _⟩
  refine R₄.of_agreeOutside ((AgreeOutside.refl {cFP} _).update rfl _) (by cells)
    (Function.update_self _ _ _) (fun i hi => ?_)
    fun a ha => (Function.update_of_ne (by cells) _ _).trans (R₄.mem a ha)
  -- local variable i of the new frame: argument i, or 0
  cell_read
  rw [val i hi]
  split_ifs with h
  · cell_read using hargs i h
  · cell_read
    rw [R.zero]
    simp [frame, List.getElem?_eq_none (not_lt.1 h)]


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.
-/




open EndStatement (Instr)

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}

/-- The code of e, and the two instructions that store T₀ in x. -/
theorem codeAt_set (h : CodeAt code pos (compileStmt G (.set x e) pos)) :
    CodeAt code pos (compileExpr e 0) ∧
      CodeAt code (pos + e.size) [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileExpr])⟩

/-- The code of s, and the code of t. -/
theorem codeAt_seq (h : CodeAt code pos (compileStmt G (.seq s t) pos)) :
    CodeAt code pos (compileStmt G s pos) ∧
      CodeAt code (pos + s.size G.F) (compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileStmt])⟩

/-- The test, the first branch, the jump over the second branch, the second branch. -/
theorem codeAt_ite (h : CodeAt code pos (compileStmt G (.ite c s t) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F)
        [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
      CodeAt code (pos + c.size + s.size G.F + 1)
        (compileStmt G t (pos + c.size + s.size G.F + 1)) := by
  rw [compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_,
    h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]

/-- The test, the body, the jump back. -/
theorem codeAt_while (h : CodeAt code pos (compileStmt G (.while c s) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG pos] := by
  rw [compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_compileCond, length_compileStmt]

/-- The arguments and the new frame, the jump to the procedure, and the two instructions that store
the result. -/
theorem codeAt_call (h : CodeAt code pos (compileStmt G (.call p args x) pos)) :
    CodeAt code pos (argsCode args 0 ++ newFrame G.F args.length (pos + callSize G.F args)) ∧
      CodeAt code (pos + (argsSize args + (2 * G.F + 4))) [.bltz cNEG (G.entry.getD p 0)] ∧
      CodeAt code (pos + callSize G.F args)
        [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET] := by
  rw [compileStmt, callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_argsCode, length_newFrame, callSize]

end layout

/-! ## The setting -/

/-- What the simulation assumes once and for all: the numbers are large enough (`Sizes`), and the
program and its code fit them. -/
structure Setting (W : ℕ) extends Sizes W where
  /-- The light program. -/
  P : Program
  /-- The code of the whole program. -/
  code : List Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    CodeAt code e (compileStmt toCodeLayout b e ++ epilogue toCodeLayout) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : CodeAt code disp (dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F

/-- An upper bound for the number of machine steps that match one step of the light language, if the
code before the dispatcher has n instructions.  Each rule of the semantics counts at least one step
and, calls apart, runs a piece of code once, which takes at most n machine steps.  A call counts two
steps, so it has 2 stepsPerStep = 4 n: at most n for its own code, n for the return sequence, 2 n
for the dispatcher. -/
def stepsPerStep (n : ℕ) : ℕ := 2 * n

/-- At most n machine steps are within the bound for c ≥ 1 steps of the language. -/
theorem le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) :
    a ≤ stepsPerStep n * c :=
  calc a ≤ stepsPerStep n * 1 := by rw [stepsPerStep]; omega
    _ ≤ stepsPerStep n * c := Nat.mul_le_mul_left _ hc

/-- At most n machine steps, followed by b machine steps that are within the bound for k steps, are
within the bound for c + k steps if c ≥ 1. -/
theorem add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c)
    (hb : b ≤ stepsPerStep n * k) : a + b ≤ stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (le_stepsPerStep_mul h hc) hb

/-- The count for a call whose code is at pos and has size + 2 instructions: size steps to enter, b
for the body, r + 2 (pos + size + 1) to leave, where r is the length of the return sequence, and 2
to store the result.  The cost a of the arguments is not needed. -/
theorem call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n)
    (hr : r ≤ n) (hb : b ≤ stepsPerStep n * k) :
    size + b + (r + 2 * (pos + size + 1)) + 2 ≤ stepsPerStep n * (a + 2 + k) := by
  rw [Nat.mul_add (stepsPerStep n), Nat.mul_add (stepsPerStep n)]
  have : stepsPerStep n * 2 = 4 * n := by rw [stepsPerStep]; omega
  omega

variable {W : ℕ} (S : Setting W)

/-- The situation before the code of the statement s runs, at nesting depth d of calls: the memory m
represents the state σ in the frame q, and the following holds. -/
structure Start (d : ℕ) (s : Stmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : CodeAt S.code pos (compileStmt S.toCodeLayout s pos)
  /-- It ends at or before the dispatcher. -/
  below : pos + s.size S.F ≤ S.disp
  /-- F local variables and 2 F + 1 temporaries are enough for s. -/
  width : s.width ≤ S.F
  /-- The state holds words. -/
  bounded : σ.Bounded S.lim
  /-- The stack has room for this frame and for F + 1 cells for each further level of calls. -/
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q

/-- The code of s, started as in `Start`, has matched a run of c steps that ends in σ': it has
taken n machine steps and left the memory m'. -/
structure Finished (s : Stmt) (σ' : State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : AgreeOutside (Writable S.toSizes q) m m'

/-- The code of s matches the run of s from σ to σ' in c steps. -/
def Simulates (d : ℕ) (s : Stmt) (σ σ' : State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), Finished S s σ' c pos q m m' n

variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}

/-- The situation before a part t of the statement runs, in the same frame. -/
theorem Start.sub (B : Start S d s σ pos q m) {t : Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : CodeAt S.code pos' (compileStmt S.toCodeLayout t pos'))
    (hpos : pos' + t.size S.F ≤ S.disp) (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim)
    (R : Rel S.toSizes σ' q m') : Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw,
    bounded := hσ, room := B.room }

/-- The room on the stack, seen from the frame of a procedure that is called. -/
theorem Start.room_succ (B : Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q := by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega

/-- The test of an if or a while that is at pos. -/
theorem Start.test (B : Start S d s σ pos q m) {c : Cond} {l : ℕ}
    (hcode : CodeAt S.code pos (compileCond c l)) (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) :
    Decides S.code S.F pos c.size l m (c.Holds σ) :=
  decides_compileCond B.toFramed B.bounded c hcode hw hs

/-! ## Statements without calls -/

/-- skip: no code, no step. -/
theorem sim_skip : Simulates S d .skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := AgreeOutside.refl _ m }⟩

/-- x := e: the code of e leaves the value in T₀, and two instructions store it in x. -/
theorem sim_set {x : ℕ} {e : Expr} (hs : e.Safe S.lim σ) :
    Simulates S d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) }
      (e.cost + 1) := by
  intro pos q m B
  obtain ⟨hx, he⟩ := Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := codeAt_set B.codeAt
  have : pos + (e.size + 2) ≤ S.disp := B.below
  -- T₀ := e
  obtain ⟨val, A⟩ := effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono temps_subset_scratch
  have run₁ := steps_straight _ pos m exprCode (straight_compileExpr e 0)
  rw [length_compileExpr] at run₁
  -- x := T₀
  obtain ⟨m₂, run₂, R₂, A₂⟩ := steps_setVar (B.toFramed.same A₁) hx setCode val (by cells)
  exact ⟨m₂, _, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := R₂
    agree := (A₁.mono scratch_subset_writable).trans A₂ }⟩

/-- The cell at a := e: the code of a and e leaves the values in T₀ and T₁, and one instruction
stores. -/
theorem sim_store {a e : Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ)
    (haddr : S.lim.Addr (a.val σ)) :
    Simulates S d (.store a e) σ
      { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } (a.cost + e.cost + 1) := by
  intro pos q m B
  obtain ⟨ha, he⟩ := Stmt.width_store_le_iff.1 B.width
  have : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  -- T₀ := a; T₁ := e
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := steps_pair B.toFramed B.codeAt ha he hsa hse
  -- the cell at T₀ := T₁
  have run₂ := run₁.trans (steps_store (codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact ⟨_, _, {
    run := run₂.cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := (B.rel.same A₁).setMem B.low haddr _
    agree := (A₁.mono scratch_subset_writable).update (mem_writable_of_addr haddr) _ }⟩

/-- s₁; s₂: the code of s₁, then the code of s₂. -/
theorem sim_seq {c₁ c₂ : ℕ} (h₁ : Exec S.lim S.P d s₁ σ σ₁ c₁)
    (ih₁ : Simulates S d s₁ σ σ₁ c₁) (ih₂ : Simulates S d s₂ σ₁ σ₂ c₂) :
    Simulates S d (.seq s₁ s₂) σ σ₂ (c₁ + c₂) := by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := codeAt_seq B.codeAt
  have : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _
    (B.sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact ⟨m₂, n₁ + n₂, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
    rel := R₂
    agree := A₁.trans A₂ }⟩

/-- if c then s₁ else s₂, when c holds: the test goes on to the code of s₁, and a jump leads over
the code of s₂. -/
theorem sim_iteTrue {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : Simulates S d s₁ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := codeAt_ite B.codeAt
  have : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the first branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
  -- the jump over the second branch
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact ⟨m₁, n₀ + 1 + n₁, {
    run := (run₂.cast_count (by omega)).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- if c then s₁ else s₂, when c fails: the test jumps to the code of s₂. -/
theorem sim_iteFalse {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ)
    (ih : Simulates S d s₂ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := codeAt_ite B.codeAt
  have : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  -- the second branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact ⟨m₁, n₀ + n₁, {
    run := (run₀.trans run₁).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- while c do s, when c fails: the test jumps to the position after the loop. -/
theorem sim_whileFalse {c : Cond} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ) :
    Simulates S d (.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := codeAt_while B.codeAt
  have : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  exact ⟨m₀, n₀, {
    run := run₀.cast_pos (by rw [Stmt.size]; omega)
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := B.rel.same A₀
    agree := A₀.mono scratch_subset_writable }⟩

/-- while c do s, when c holds: the test goes on to the code of s, a jump leads back to the test,
and the loop runs again. -/
theorem sim_whileTrue {c : Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : Simulates S d s σ σ₁ k₁)
    (ih₂ : Simulates S d (.while c s) σ₁ σ₂ k₂) :
    Simulates S d (.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) := by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := codeAt_while B.codeAt
  have : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the body
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _
    (B.sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
  -- the jump back
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  -- the loop again
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _
    (B.sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact ⟨m₃, n₀ + 1 + n₁ + n₃, {
    run := (run₂.trans run₃).cast_count (by omega)
    le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (add_le_stepsPerStep_mul (by omega) (by omega) le₁)
        le₃
    rel := R₃
    agree := ((A₀.mono scratch_subset_writable).trans A₁).trans A₃ }⟩

/-! ## Calls -/

section call

variable {p x : ℕ} {args : List Expr}

/-- Entering a procedure: the arguments, the new frame with the position to return to, and the jump
to the entry e.  Afterwards the memory represents the state in which the procedure starts, in the
frame q + F + 1, and the stack cell before that frame holds the position after the jump.  Of the
stack, only cells from q + F on have changed. -/
theorem steps_callEnter (B : Start S d (.call p args x) σ pos q m)
    (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hd : d < S.lim.depth) {e : ℕ}
    (he : S.entry[p]? = some e) :
    ∃ m₂, Steps S.code (callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
      Rel S.toSizes ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
      m₂ (cStack (q + S.F)) = wd W ((pos + callSize S.F args : ℕ) : ℤ) ∧
      AgreeOutside (Writable S.toSizes (q + S.F)) m m₂ := by
  obtain ⟨-, hlen, hwa⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := codeAt_call B.codeAt
  have : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  -- the arguments: there are at most F of them, each of width at most F
  obtain ⟨vals, A⟩ := effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono temps_subset_scratch
  -- the new frame
  obtain ⟨R₂, hret, A₂⟩ := effects_newFrame (B.toFramed.same A₁)
    ((Nat.le_add_right _ _).trans (B.room_succ hd)) args (by simpa using vals)
    (ret := pos + callSize S.F args) (by omega)
  have run₂ := steps_straight _ pos m frameCode
    (List.forall_mem_append.2 ⟨straight_argsCode _ _, straight_newFrame _ _ _⟩)
  rw [effects_append, List.length_append, length_argsCode, length_newFrame] at run₂
  -- the jump
  exact ⟨_, (run₂.trans (steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count
    (by rw [callSize]; omega), R₂, hret, (A₁.mono scratch_subset_writable).trans A₂⟩

/-- Leaving a procedure whose frame is q + F + 1, when the stack cell before that frame holds the
position ret: the return sequence and the dispatcher.  The machine arrives at ret; RET holds the
result (local variable 0), FP points to the frame q, and otherwise only scratch cells have
changed. -/
theorem steps_callLeave (S : Setting W) {ret : ℕ} (R : Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : CodeAt S.code pos (epilogue S.toCodeLayout))
    (hret : m (cStack (q + S.F)) = wd W ret) (hlt : ret < S.disp) (hQ : q + S.F + 1 ≤ S.Q)
    (hF : 0 < S.F) :
    ∃ m', Steps S.code (epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
      m' cFP = wd W (cStack q) ∧ m' cRET = wd W (σ.loc 0) ∧
      AgreeOutside (insert cFP (Scratch S.F)) m m' := by
  have hN := S.offsets_le
  -- RET := the cell at FP, which is local variable 0
  have run₁ := steps_load (i := cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ := (AgreeOutside.refl (Scratch S.F) m).update (a := cRET) (by cells) (wd W (σ.loc 0))
  -- ADDR := FP + 2, the address of the stack cell before the frame
  have run₂ := run₁.trans (steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [cStack_succ_add] at run₂
  have A₂ := A₁.update (a := cADDR) (by cells) (wd W (cStack (q + S.F)))
  -- RR := the cell at ADDR, which holds ret
  have run₃ := run₂.trans (steps_load hcode.tail.tail (Function.update_self _ _ _)
    (S.inRange_stack (by omega)))
  rw [A₂.read (by cells) hret] at run₃
  have A₃ := A₂.update (a := cRR) (by cells) (wd W ret)
  -- FP := FP + 2 (F + 1), the frame of the caller
  have run₄ := run₃.trans (steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, cStack_add] at run₄
  -- the jump to the dispatcher
  have run₅ := run₄.trans (steps_jump hcode.tail.tail.tail.tail
    (by cell_read using (R.same A₃).neg) S.inRange_neg_one)
  -- the dispatcher, which leaves -1 in RR
  have run₆ := run₅.trans (steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
    (by cell_read using (R.same A₃).one) (by cell_read))
  exact ⟨_, run₆, by cell_read, by cell_read,
    ((A₃.mono (by cells)).update (by cells) _).update (by cells) _⟩

/-- x := p(args): enter, the body, leave, store the result. -/
theorem sim_call {body : Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hp : S.P[p]? = some body) (hd : d < S.lim.depth)
    (ih : Simulates S (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    Simulates S d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
      ((args.map Expr.cost).sum + 2 + k) := by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.room_succ hd
  -- enter
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := steps_callEnter B hsa hd he
  -- the body, in the frame q + F + 1
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih e (q + S.F + 1) m₁
    { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
      width := S.width body (List.mem_of_getElem? hp),
      bounded := bounded_callFrame B.bounded args hsa, room := hroom }
  -- the body writes the stack only from its frame on, so the position to return to is still there
  have hret₂ := A₂.read (a := cStack (q + S.F)) (by cells) hret
  -- leave
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ := steps_callLeave S R₂
    (procCode.right.cast_pos (by rw [length_compileStmt])) hret₂ (by omega) (by omega)
    (Nat.zero_lt_of_lt hx)
  -- since the call began, the stack has changed only from cell q + F on: the local variables of the
  -- caller are as before, and the memory is as the procedure left it
  have A : AgreeOutside (Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (writable_subset_writable (by omega)))).trans
      (A₃.mono (Set.insert_subset (by cells) scratch_subset_writable))
  have I₃ : Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ := ⟨R₂.of_agreeOutside A₃ (by cells) hfp
    (fun y hy => A.read (by cells) (B.rel.loc y hy))
    fun a ha => A₃.read (by cells) (R₂.mem a ha), hq, B.high⟩
  -- store the result
  obtain ⟨m₄, run₄, R₄, A₄⟩ := steps_setVar I₃ hx resultCode hres (by cells)
  exact ⟨m₄, _, {
    run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := call_le_stepsPerStep_mul hpos (by omega) le₂
    rel := R₄
    agree := (A.mono (writable_subset_writable (by omega))).trans A₄ }⟩

end call

/-! ## The theorem -/

/-- **The simulation theorem.**  The code of a statement matches every run of the statement. -/
theorem sim (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) :
    Simulates S d s σ σ' c := by
  induction h with
  | skip => exact sim_skip
  | set hs => exact sim_set hs
  | store hsa hse haddr => exact sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact sim_iteFalse hs fails ih
  | whileFalse hs fails => exact sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact sim_call hsa hp hd ih

end Light.Compiler
