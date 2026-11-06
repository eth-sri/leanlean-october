/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import EndStatement
import ThreeSumApsp.Util.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/


namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/

/-- The integer v is the signed value of a W-bit word. -/
def InRange (W : ℕ) (v : ℤ) : Prop := -(2 : ℤ) ^ W ≤ 2 * v ∧ 2 * v < (2 : ℤ) ^ W

/-- The word of an integer. -/
abbrev wd (W : ℕ) (v : ℤ) : BitVec W := BitVec.ofInt W v

variable {v : ℤ}

/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd (h : InRange W v) : (wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : wd W w.toInt = w := BitVec.ofInt_toInt

theorem wd_add (a b : ℤ) : wd W a + wd W b = wd W (a + b) := by grind [BitVec.ofInt_add]

theorem wd_mul (a b : ℤ) : wd W a * wd W b = wd W (a * b) := by grind [BitVec.ofInt_mul]

theorem wd_sub (a b : ℤ) : wd W a - wd W b = wd W (a - b) := by
  grind [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem wd_one : (1 : BitVec W) = wd W 1 := BitVec.eq_of_toNat_eq rfl

/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros. -/
theorem loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by
  rfl

/-- The negative cells of the initial memory hold zeros. -/
theorem loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0 := by decide) :
    loadWords W ws a = wd W 0 := by
  grind [loadWords]

/-! ## Configurations and single steps -/

/-- A configuration of the machine: the position of the next instruction and the memory. -/
structure Cfg (W : ℕ) where
  pc : ℕ
  mem : ℤ → BitVec W

/-- One step: the next configuration, or the verdict. -/
def step (P : List Instr) (c : Cfg W) : Cfg W ⊕ Bool :=
  let m := c.mem
  let write (i : ℤ) (v : BitVec W) :=
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

variable {c' c : Cfg W}

theorem Steps.one (h : step P c = .inl c') : Steps P 1 c c' := by tauto

variable {n : ℕ}

/-- One run after the other. -/
theorem Steps.trans {k : ℕ} {c₁ c₂ : Cfg W} (h₁ : Steps P n c c₁) (h₂ : Steps P k c₁ c₂) :
    Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simp_all
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {p p' : ℕ} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := by simp_all

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n' : ℕ} (h : Steps P n c c') (hn : n = n' := by omega) :
    Steps P n' c c' := by simp_all


theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  grind [exec, step]

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by grind [exec_succ]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by grind [exec_succ]

/-- A run that reaches a verdict. -/
theorem exec_of_steps {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    grind [exec_succ_of_step]

/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => tauto
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => simp_all [exec_succ_of_verdict]
    | inl n =>
      simp_all [exec_succ_of_step]

/-! ## Pieces of code -/

/-- The program P has the instructions of the list l from position pos on. -/
def CodeAt (P : List Instr) (pos : ℕ) (l : List Instr) : Prop := l <+: P.drop pos

/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List Instr) : CodeAt l 0 l := l.prefix_refl

variable {pos : ℕ} {l₂ l₁ : List Instr}

/-- The first part of a piece of code. -/
theorem CodeAt.left (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  grind [List.drop_drop, List.append_assoc, List.drop_left]

variable {l : List Instr}

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {i : Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by grind
  simp_all

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {i : Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l :=
  CodeAt.right (l₁ := [i]) h

variable {pos' : ℕ}

/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos (h : CodeAt P pos l) (hp : pos = pos') :
    CodeAt P pos' l := by simp_all

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
  simp [effects]

theorem step_straight {i : Instr} (h : P.getD c.pc .reject = i)
    (hi : Straight i) : step P c = .inl ⟨c.pc + 1, effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    grind
  cases i <;> simp only [Straight] at hi <;> simp only [step, h, effect, write, wd_one]

variable {rest : List Instr}

/-- One instruction that only changes the memory. -/
theorem steps_instr {i : Instr}
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
      (ih _ _ hcode.tail hl).cast_pos (by grind)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}


/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b := by assumption) :
    effect (.add i j k) m = Function.update m i (wd W (a + b)) := by
  grind [effect, wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by
  grind [effect, wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by
  grind [effect, wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by
  grind [effect, toInt_wd]

/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by
  grind [effect, toInt_wd]

variable {rest : List Instr} {pos : ℕ}

theorem steps_add (hcode : CodeAt P pos (.add i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a + b))⟩ :=
  effect_add i hj hk ▸ steps_instr hcode trivial m

theorem steps_sub (hcode : CodeAt P pos (.sub i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b := by assumption) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a - b))⟩ :=
  effect_sub i hj hk ▸ steps_instr hcode trivial m

theorem steps_load (hcode : CodeAt P pos (.load i j :: rest))
    (hj : m j = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  effect_load i hj ha ▸ steps_instr hcode trivial m

theorem steps_store (hcode : CodeAt P pos (.store i j :: rest))
    (hi : m i = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  effect_store j hi ha ▸ steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {l : ℕ} {c : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v := by simp_all) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  apply Steps.one
  simp only [step, hcode.head, hc, toInt_wd hv]

/-- A run that ends with a branch on the sign of v, where v is negative if and only if p fails. -/
theorem Steps.branch {l : ℕ} {m : ℤ → BitVec W} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by
  grind

theorem step_accept (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by
  grind [step]

theorem step_reject (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by
  grind [step]

/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

/-- The memory m' differs from m only in cells of the set s. -/
def AgreeOutside (s : Set ℤ) (m m' : ℤ → BitVec W) : Prop := Set.EqOn m' m sᶜ

theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : AgreeOutside s m m := by tauto

theorem AgreeOutside.trans (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' :=
  by tauto

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside t m₂ m₃) :
    AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  by aesop

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (by grind) _ _).trans (h hx)

/-- The instruction writes no cell outside s, whatever the memory holds. -/
def WritesIn (s : Set ℤ) : Instr → Prop
  | .one i | .add i _ _ | .sub i _ _ | .mul i _ _ | .load i _ => i ∈ s
  | .store _ _ => False
  | _ => True

theorem WritesIn.mono {i : Instr} (h : WritesIn s i) (hst : s ⊆ t) : WritesIn t i := by
  cases i <;> aesop

theorem agreeOutside_effect {i : Instr} (h : WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effect i m) := by
  cases i <;>
    first | exact (AgreeOutside.refl s m).update h _ | tauto

/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by
  induction l generalizing m with
  | nil => tauto
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (agreeOutside_effect hi m).trans (by simp_all)
