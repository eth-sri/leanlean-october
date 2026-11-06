/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.Lattice
public import Mathlib.Tactic

/-!
# Cofinality of increasing lattice boxes

Nested exhaustive sequences of finite lattice boxes eventually contain each
fixed finite lattice box. The canonical origin-centered boxes are nested and
exhaust the square lattice.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

section

variable {c : ℕ → LatticeVertex} {r : ℕ → ℕ} (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
include hnest

/-- Nesting propagates box containment to every later index. -/
theorem latticeBox_subset_of_nested 
    {m n : ℕ} (hmn : m ≤ n) :
    latticeBox (c m) (r m) ⊆ latticeBox (c n) (r n) := Nat.le.rec subset_rfl (fun {n} hmn ih => LE.le.trans ih (hnest n)) hmn

/-- A nested exhaustive sequence of boxes eventually contains any fixed box. -/
theorem latticeBox_subset_eventually_of_nested_exhaustive
    
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n))
    (a : LatticeVertex) (R : ℕ) :
    ∃ N, ∀ n ≥ N, latticeBox a R ⊆ latticeBox (c n) (r n) := let i := fun v => Classical.choose (hexhaust v);
                                                             let N := (latticeBox a R).sup i;
                                                             Exists.intro N fun n hn v hv =>
                                                               latticeBox_subset_of_nested hnest (LE.le.trans (Finset.le_sup hv) hn) (Classical.choose_spec (hexhaust v))

end

/-- The canonical origin-centered boxes are nested. -/
theorem origin_latticeBox_nested (n : ℕ) :
    latticeBox (0, 0) n ⊆ latticeBox (0, 0) (n + 1) :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.FK.latticeBox_mono]

/-- Every lattice vertex lies in some canonical origin-centered box. -/
theorem origin_latticeBox_exhaustive (v : LatticeVertex) :
    ∃ n, v ∈ latticeBox (0, 0) n := by
  refine ⟨max v.1.natAbs v.2.natAbs, ?_⟩
  rw [mem_latticeBox]
  grind

end PottsDiscontinuity.FK
