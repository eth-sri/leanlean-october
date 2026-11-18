module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# The primewise identity

PD §4 (`mem:prime-factor`, `mem:orphan-identity`, `mem:prefix`, `mem:suffix`;
`blueprint/one_sided_type_ii.md` §5.5, M1). Fix a prime `p` and a path of visits
`j = 0, …, N` with lines `L_j ∈ {0, …, p}` (the lines `[z_j]_p`), damping defects
`η'_j = 1 - q_j`, and the set `A` of visits where `p` is active. Averaged over a uniform
line `ℓ ∈ {0, …, p}`, the factor of `p` is
`E = (p + 1)⁻¹ ∑_ℓ ∏_{j ∈ A} [ℓ = L_j] ∏_{j ∉ A} (1 - η'_j [ℓ = L_j])`.

* `primeFactor_eq_orphan`: with `A = ∅`,
  `E = b' + (p + 1)⁻¹ ∑_{a < c} η'_a η'_c [L_a = L_c] ∏_{a < j < c} (1 - η'_j [L_j = L_a])`,
  where `b' = 1 - (p + 1)⁻¹ ∑_j η'_j`. Expand the product over subsets. The empty and
  singleton subsets give `b'`. A larger subset is grouped by its first and last element
  `a < c`, and summing its internal part gives the product.
* `primeFactor_eq_active`: with `A ≠ ∅` and all active lines equal to `L*`,
  `E = (p + 1)⁻¹ ∏_{j ∉ A} (1 - η'_j [L_j = L*])`. If two active lines differ, `E = 0`.
* `prod_one_sub_eq_prefix`: the finite telescoping identity
  `∏_{j < a} (1 - x_j) = 1 - ∑_{h < a} x_h ∏_{h < j < a} (1 - x_j)`, which attaches at most
  one ghost to each end of an active interval.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

/-- The averaged factor of one prime: `(p + 1)⁻¹ ∑_ℓ ∏_{j ∈ A} [ℓ = L_j] ∏_{j ∉ A}
(1 - η'_j [ℓ = L_j])`, over visits `j ∈ range (N + 1)`. -/
noncomputable def primeFactor (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ((p : ℝ) + 1)⁻¹ * ∑ ℓ ∈ range (p + 1),
    (∏ j ∈ A, if ℓ = L j then (1 : ℝ) else 0) *
      ∏ j ∈ (range (N + 1)).filter (· ∉ A), (1 - η' j * if ℓ = L j then 1 else 0)

end Erdos408.OneSided
