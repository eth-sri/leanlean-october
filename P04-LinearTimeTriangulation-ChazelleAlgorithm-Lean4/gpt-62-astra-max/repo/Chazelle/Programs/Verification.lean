module

public import Chazelle.Programs.Tactics
public import Chazelle.Programs.Address

/-! # Discharging block specifications

In a straight-line proof there are three different kinds of obligations: bounds for the
instructions, reads at known addresses, and frame conditions at an arbitrary address. The same
read-over-write rules handle the last two, using arithmetic to establish non-aliasing.
-/

public section
namespace Chazelle.Programs
open Lean.Parser.Tactic

/-- Rewrite using conditional register/memory equations, proving their side conditions. -/
macro "frame_simp" "[" hs:simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := first | assumption | decide | omega) only
    [Machine.upd_same, Machine.upd_other, $hs,*])

/-- Discharge the bounds and postcondition after symbolic execution. The optional facts
identify the input values of registers and cells for this block. -/
macro "block_post" "[" more:simpLemma,* "]" : tactic =>
  `(tactic| (repeat' first | apply And.intro | intro
             all_goals first
               | rfl | assumption
               | solve | config_simp <;> omega
               | (config_simp <;> simp (disch := first | assumption | decide | omega) only
                    [Machine.upd_same, Machine.upd_other, *, $more,*] <;> first | omega | address_omega)))

macro "block_post" : tactic => `(tactic| block_post [])

/-- Verify a whole straight-line block. -/
macro "verify_block" "[" hs:simpLemma,* "]" : tactic =>
  `(tactic| (exec_block <;> block_post [$hs,*]))

macro "verify_block" : tactic => `(tactic| verify_block [])

end Chazelle.Programs
