module

public meta import Chazelle.Arithmetic

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
  core_grind


section
variable {ins : Instr} {p q : Program} {base : ℕ}
theorem SubAt.cons_iff :
    SubAt (ins :: p) q base ↔ q[base]? = some ins ∧ SubAt p q (base + 1) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 ins rfl, fun i ins' hi => ?_⟩
    have := h (i + 1) ins' (by simp_all)
    simp_all +arith
  ram_grind

section
variable (h : SubAt (ins :: p) q base)
include h
theorem SubAt.head :
    q[base]? = some ins :=
  (SubAt.cons_iff.mp h).1

theorem SubAt.tail :
    SubAt p q (base + 1) :=
  (SubAt.cons_iff.mp h).2



end

end

theorem SubAt.singleton_iff {ins : Instr} {q : Program} {base : ℕ} :
    SubAt [ins] q base ↔ q[base]? = some ins := by
  simp [SubAt.cons_iff]

theorem SubAt.append_iff {p₁ p₂ q : Program} {base : ℕ} :
    SubAt (p₁ ++ p₂) q base ↔ SubAt p₁ q base ∧ SubAt p₂ q (base + p₁.length) := by
  constructor
  · intro h
    refine ⟨fun i ins hi => h i ins ?_, fun i ins hi => ?_⟩
    · grind
    · have := h (p₁.length + i) ins (by
        grind)
      simp_all +arith
  ram_grind

section
variable {p₁ p₂ q : Program} {base : ℕ} (h : SubAt (p₁ ++ p₂) q base)
include p₂ h
theorem SubAt.of_append_left :
    SubAt p₁ q base :=
  (SubAt.append_iff.mp h).1

theorem SubAt.of_append_right :
    SubAt p₂ q (base + p₁.length) :=
  (SubAt.append_iff.mp h).2


end

section
variable (p₁ p₂ : Program)

/-- The first half of a concatenation sits at address `0`. -/
theorem SubAt.append_left : SubAt p₁ (p₁ ++ p₂) 0 := by
  intro i ins hi
  grind


/-! ### Shifting the program counter -/


end






/-! ### The relocation theorem -/

end

end Machine

end Chazelle
