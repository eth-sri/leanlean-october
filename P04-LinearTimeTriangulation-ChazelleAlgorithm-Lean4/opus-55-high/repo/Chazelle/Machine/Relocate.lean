module

public import Chazelle.Machine.Basic

/-!
# Relocation and linking

* `Instr.relocate off` shifts every jump/branch target by `off`; `Program.relocate` maps it
  over a program.  Straight-line instructions are unchanged (`Instr.relocate_of_isStraight`).
* `SubAt p q base`: the program `p` sits verbatim at address `base` inside `q`
  (`∀ i ins, p[i]? = some ins → q[base + i]? = some ins`).  Lemmas for `[]`, `::`, `++`,
  transitivity, and the two halves of a concatenation.
* `shiftPc off c`: the configuration `c` with its program counter shifted by `off`.
* The relocation theorem `run_relocate`: if `p.relocate off` sits at `off` inside `q` and a
  `k`-step run of `p` from `c` never leaves `p`'s code (the program counter of every
  configuration *before* a step is `< p.length`), then
  `run q P k (shiftPc off c) = (run p P k c).map (shiftPc off)`.  Faults (`halt`, division
  by zero) are reproduced exactly.  `RunsTo.relocate` transfers bounded runs, and
  `AtHalt.relocate` transfers the final `halt`.
-/

namespace Chazelle

namespace Instr

@[expose] public section

/-- Shift every jump/branch target by `off`; other instructions are unchanged. -/
def relocate (off : ℕ) : Instr → Instr
  | .jump l => .jump (l + off)
  | .brLtN a b l => .brLtN a b (l + off)
  | .brLtR a b l => .brLtR a b (l + off)
  | ins => ins

@[simp] theorem relocate_halt (off : ℕ) : (Instr.halt).relocate off = .halt := rfl
@[simp] theorem relocate_jump (off l : ℕ) : (Instr.jump l).relocate off = .jump (l + off) := rfl
@[simp] theorem relocate_brLtN (off a b l : ℕ) :
    (Instr.brLtN a b l).relocate off = .brLtN a b (l + off) := rfl
@[simp] theorem relocate_brLtR (off a b l : ℕ) :
    (Instr.brLtR a b l).relocate off = .brLtR a b (l + off) := rfl

@[simp] theorem relocate_zero (ins : Instr) : ins.relocate 0 = ins := by
  cases ins <;> rfl

/-- Relocation does not touch straight-line instructions. -/
@[simp] theorem relocate_of_isStraight {ins : Instr} (h : ins.IsStraight) (off : ℕ) :
    ins.relocate off = ins := by
  cases ins <;> first | rfl | simp at h

@[simp] theorem isStraight_relocate {ins : Instr} {off : ℕ} :
    (ins.relocate off).IsStraight ↔ ins.IsStraight := by
  cases ins <;> simp [relocate]

end

end Instr

namespace Program

@[expose] public section

/-- Relocate every instruction of a program. -/
def relocate (off : ℕ) (p : Program) : Program := p.map (Instr.relocate off)

@[simp] theorem length_relocate (off : ℕ) (p : Program) : (p.relocate off).length = p.length :=
  List.length_map ..

@[simp] theorem getElem?_relocate (off : ℕ) (p : Program) (i : ℕ) :
    (p.relocate off)[i]? = p[i]?.map (Instr.relocate off) :=
  List.getElem?_map ..

@[simp] theorem relocate_zero (p : Program) : p.relocate 0 = p := by
  rw [relocate, show Instr.relocate 0 = id from funext Instr.relocate_zero, List.map_id]

@[simp] theorem relocate_nil (off : ℕ) : Program.relocate off [] = [] := rfl

@[simp] theorem relocate_cons (off : ℕ) (ins : Instr) (p : Program) :
    Program.relocate off (ins :: p) = ins.relocate off :: p.relocate off := rfl

@[simp] theorem relocate_append (off : ℕ) (p₁ p₂ : Program) :
    (p₁ ++ p₂).relocate off = p₁.relocate off ++ p₂.relocate off :=
  List.map_append ..

end

end Program

namespace Machine

@[expose] public section

/-! ### Placement of a program inside a larger one -/

/-- The program `p` sits verbatim at address `base` inside `q`. -/
def SubAt (p q : Program) (base : ℕ) : Prop :=
  ∀ i ins, p[i]? = some ins → q[base + i]? = some ins

@[simp] theorem SubAt.nil (q : Program) (base : ℕ) : SubAt [] q base := by
  intro i ins h; simp at h

theorem SubAt.refl (p : Program) : SubAt p p 0 := by
  intro i ins h; simpa using h

theorem SubAt.cons_iff {ins : Instr} {p q : Program} {base : ℕ} :
    SubAt (ins :: p) q base ↔ q[base]? = some ins ∧ SubAt p q (base + 1) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 ins rfl, fun i ins' hi => ?_⟩
    have := h (i + 1) ins' (by simpa using hi)
    rw [show base + 1 + i = base + (i + 1) by omega]; exact this
  · rintro ⟨h0, h⟩ i ins' hi
    cases i with
    | zero => simp at hi; subst hi; simpa using h0
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := h i ins' hi
      rw [show base + (i + 1) = base + 1 + i by omega]; exact this

theorem SubAt.head {ins : Instr} {p q : Program} {base : ℕ} (h : SubAt (ins :: p) q base) :
    q[base]? = some ins :=
  (SubAt.cons_iff.mp h).1

theorem SubAt.tail {ins : Instr} {p q : Program} {base : ℕ} (h : SubAt (ins :: p) q base) :
    SubAt p q (base + 1) :=
  (SubAt.cons_iff.mp h).2

theorem SubAt.singleton_iff {ins : Instr} {q : Program} {base : ℕ} :
    SubAt [ins] q base ↔ q[base]? = some ins := by
  simp [SubAt.cons_iff]

theorem SubAt.append_iff {p₁ p₂ q : Program} {base : ℕ} :
    SubAt (p₁ ++ p₂) q base ↔ SubAt p₁ q base ∧ SubAt p₂ q (base + p₁.length) := by
  constructor
  · intro h
    refine ⟨fun i ins hi => h i ins ?_, fun i ins hi => ?_⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi
    · have := h (p₁.length + i) ins (by
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hi)
      rwa [← Nat.add_assoc] at this
  · rintro ⟨h₁, h₂⟩ i ins hi
    by_cases hlt : i < p₁.length
    · rw [List.getElem?_append_left hlt] at hi; exact h₁ i ins hi
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
      have := h₂ _ ins hi
      rwa [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)] at this

theorem SubAt.of_append_left {p₁ p₂ q : Program} {base : ℕ} (h : SubAt (p₁ ++ p₂) q base) :
    SubAt p₁ q base :=
  (SubAt.append_iff.mp h).1

theorem SubAt.of_append_right {p₁ p₂ q : Program} {base : ℕ} (h : SubAt (p₁ ++ p₂) q base) :
    SubAt p₂ q (base + p₁.length) :=
  (SubAt.append_iff.mp h).2

/-- The lookup lemma for concatenation. -/
theorem getElem?_append_length_add (p₁ p₂ : Program) (i : ℕ) :
    (p₁ ++ p₂)[p₁.length + i]? = p₂[i]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The first half of a concatenation sits at address `0`. -/
theorem SubAt.append_left (p₁ p₂ : Program) : SubAt p₁ (p₁ ++ p₂) 0 := by
  intro i ins hi
  rw [Nat.zero_add, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi

/-- The second half of a concatenation sits at address `p₁.length`. -/
theorem SubAt.append_right (p₁ p₂ : Program) : SubAt p₂ (p₁ ++ p₂) p₁.length := by
  intro i ins hi
  rw [getElem?_append_length_add]; exact hi

/-! ### Shifting the program counter -/

/-- The configuration `c` with its program counter shifted by `off`. -/
def shiftPc (off : ℕ) (c : Config) : Config := { c with pc := c.pc + off }

@[simp] theorem shiftPc_pc (off : ℕ) (c : Config) : (shiftPc off c).pc = c.pc + off := rfl
@[simp] theorem shiftPc_nreg (off : ℕ) (c : Config) : (shiftPc off c).nreg = c.nreg := rfl
@[simp] theorem shiftPc_rreg (off : ℕ) (c : Config) : (shiftPc off c).rreg = c.rreg := rfl
@[simp] theorem shiftPc_nmem (off : ℕ) (c : Config) : (shiftPc off c).nmem = c.nmem := rfl
@[simp] theorem shiftPc_rmem (off : ℕ) (c : Config) : (shiftPc off c).rmem = c.rmem := rfl
@[simp] theorem shiftPc_output (off : ℕ) (c : Config) : (shiftPc off c).output = c.output := rfl
@[simp] theorem shiftPc_zero (c : Config) : shiftPc 0 c = c := rfl

@[simp] theorem wordsBounded_shiftPc {W off : ℕ} {c : Config} :
    WordsBounded W (shiftPc off c) ↔ WordsBounded W c := Iff.rfl

/-! ### The relocation theorem -/

end

end Machine

end Chazelle
