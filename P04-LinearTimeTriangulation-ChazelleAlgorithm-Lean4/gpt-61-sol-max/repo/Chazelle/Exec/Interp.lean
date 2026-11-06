module

public import Chazelle.Spec
public import Std.Data.HashMap

/-!
# An executable exact-rational interpreter for the RAM of `Chazelle/Spec.lean`

The machine semantics `Chazelle.step` / `Chazelle.run` works over `ℝ` and is therefore
noncomputable.  This file defines a computable interpreter with the *same* instruction
semantics over `ℚ`:

* `QPolygon := List (ℚ × ℚ)`: a polygon with rational vertices;
* `QConfig`: a configuration whose register files and memories are persistent hash maps with
  default value `0` (`Std.HashMap`), so that execution is fast;
* `stepWith fetch size vtx c`: one instruction, parametrised by how the program and the input
  are looked up; `stepQ prog Pq` is the instance for list-shaped programs and polygons;
* `runSteps`: exactly `k` instructions (the analogue of `Chazelle.run`);
* `runLoop` / `runQOutcome` / `runQ`: a fuel-bounded run until `halt`, a fault, or fuel
  exhaustion, reporting the final configuration and the number of executed instructions.
  `runQ` looks the program and the input up in arrays (constant-time access) and is proved
  equal to the list-based semantics in `runQ_eq`.

The simulation theorem relating all this to the real semantics is in
`Chazelle/Exec/Simulation.lean`.
-/

namespace Chazelle

namespace Exec

open Std

@[expose] public section


/-- A machine configuration over `ℚ`.  Register files and memories are hash maps; an absent key
denotes the value `0`, exactly like the all-zero initial configuration of the specification. -/
structure QConfig where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers (absent = `0`). -/
  nreg : HashMap ℕ ℕ
  /-- Rational registers (absent = `0`). -/
  rreg : HashMap ℕ ℚ
  /-- Natural memory (absent = `0`). -/
  nmem : HashMap ℕ ℕ
  /-- Rational memory (absent = `0`). -/
  rmem : HashMap ℕ ℚ
  /-- The triangles emitted so far, in order. -/
  output : List Polygon.Triangle

namespace QConfig

section
variable (c : QConfig)
include c

/-- Read rational register `r`. -/
def rr (r : ℕ) : ℚ := c.rreg.getD r 0


/-- Read rational memory cell `a`. -/
def rm (a : ℕ) : ℚ := c.rmem.getD a 0


end

end QConfig


/-! ## Basic facts -/

end

end Exec

end Chazelle
