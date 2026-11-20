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

end

end Instr

namespace Program

@[expose] public section

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

/-- The first half of a concatenation sits at address `0`. -/
theorem SubAt.append_left (p₁ p₂ : Program) : SubAt p₁ (p₁ ++ p₂) 0 := by
  intro i ins hi
  rw [Nat.zero_add, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi

/-! ### Shifting the program counter -/

/-! ### The relocation theorem -/

end

end Machine

end Chazelle
