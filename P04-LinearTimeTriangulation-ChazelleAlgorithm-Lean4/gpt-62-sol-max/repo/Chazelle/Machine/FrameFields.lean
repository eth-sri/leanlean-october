module

public import Chazelle.Machine.Basic

namespace Chazelle.Machine

@[expose] public section

/-- The real heap and the output are untouched. -/
abbrev RealMemOutputEq (c c' : Config) : Prop := c'.rmem = c.rmem ∧ c'.output = c.output

/-- Neither the heaps nor the output change. -/
abbrev MemOutputEq (c c' : Config) : Prop := c'.nmem = c.nmem ∧ RealMemOutputEq c c'

/-- A natural-register block does not change the real registers, heaps, or output. -/
abbrev NatRegFrame (c c' : Config) : Prop :=
  c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ RealMemOutputEq c c'

/-- All natural registers other than the specified destination are untouched. -/
abbrev NRegEqExcept (r : ℕ) (c c' : Config) : Prop := ∀ i, i ≠ r → c'.nreg i = c.nreg i

/-- Natural registers outside the half-open register bank are untouched. -/
abbrev NRegEqOutside (lo hi : ℕ) (c c' : Config) : Prop :=
  ∀ i, (i < lo ∨ hi ≤ i) → c'.nreg i = c.nreg i

end

end Chazelle.Machine
