module

public import Erdos408.Mertens
public import Erdos408.Extraction.Defs

/-!
# Prime sums for the proxy estimates

Natural-number bounds for membership in `primesIcc`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

theorem mem_primesIcc {a b : ℝ} {p : ℕ} :
    p ∈ primesIcc a b ↔ p.Prime ∧ ⌈a⌉₊ ≤ p ∧ p ≤ ⌊b⌋₊ := by
  simp only [primesIcc, mem_filter, mem_Icc]
  tauto

end Erdos408.TypeII
