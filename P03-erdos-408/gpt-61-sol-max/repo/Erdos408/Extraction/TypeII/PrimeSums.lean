module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.Extraction.Allocation.Euler

public import Erdos408.Mertens
public import Erdos408.Extraction.Defs

/-!
# Prime sums for the proxy estimates

Mertens' third theorem in the form `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`, and the
identification of the prime sets `primesIcc 2 y`, `primesIoc 1 y` and
`{p ≤ N prime}` used by the Euler-product bounds.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

theorem mem_primesIcc  {a b}   {p}  :
    p ∈ primesIcc a b ↔ p.Prime ∧ ⌈a⌉₊ ≤ p ∧ p ≤ ⌊b⌋₊ := by
  simp only [primesIcc, mem_filter, mem_Icc]
  tauto



/-- Mertens' third theorem, lower bound: `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`. -/
alias mertens_third_lower := _root_.Erdos408.exists_prod_one_sub_ge

end Erdos408.TypeII
