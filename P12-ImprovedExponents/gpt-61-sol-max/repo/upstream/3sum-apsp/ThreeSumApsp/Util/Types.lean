module
public import Mathlib.Data.Matrix.Basic

@[expose] public section

namespace Light
/-- Integer-valued storage, used for both locals and shared memory. -/
abbrev Memory := Nat → Int
/-- Solver time as a function of its two size parameters. -/
abbrev SolverTime := Nat → Nat → Nat
/-- The running time of a call from its list of size arguments. -/
abbrev InputTime := List Nat → Nat
end Light

namespace ThreeSumApsp
/-- An integer matrix with dimensions recorded in its type. -/
abbrev IntMatrix (m n : Nat) := Matrix (Fin m) (Fin n) Int
end ThreeSumApsp
