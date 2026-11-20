module

public import RequestProject.RACGDescent

@[expose] public section

/-!
# Medians in the Cayley graph of a right-angled Coxeter group

This file proves the combinatorial heart of Gromov's criterion for the cube complexes used in
the paper:

* `FiniteChains.RACG.len_mul_of_no_common_desc` — if two elements have no common left descent,
  the lengths of their "difference" add up;
* `FiniteChains.RACG.exists_median` — any three elements of the group have a median vertex in
  the Cayley graph;
* `FiniteChains.RACG.median_unique` — the median is unique.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

theorem gen_inv (s : V) : (gen A s)⁻¹ = gen A s :=
  inv_eq_of_mul_eq_one_left (gen_mul_gen A s)

end RACG
end FiniteChains
