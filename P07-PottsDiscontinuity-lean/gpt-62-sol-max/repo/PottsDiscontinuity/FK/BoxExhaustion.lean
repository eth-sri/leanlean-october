/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Lattice
public import Mathlib.Tactic
public import Mathlib.Topology.Order.OrderClosed

/-!
# Cofinality of increasing lattice boxes

Nested exhaustive sequences of finite lattice boxes eventually contain each
fixed finite lattice box. The canonical origin-centered boxes are nested and
exhaust the square lattice.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

/-- Nesting propagates box containment to every later index. -/
theorem latticeBox_subset_of_nested {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    {m n : ℕ} (hmn : m ≤ n) :
    latticeBox (c m) (r m) ⊆ latticeBox (c n) (r n) := by
  induction hmn with
  | refl => exact subset_rfl
  | @step n hmn ih => exact ih.trans (hnest n)

/-- A nested exhaustive sequence of boxes eventually contains any fixed box. -/
theorem latticeBox_subset_eventually_of_nested_exhaustive
    {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n))
    (a : LatticeVertex) (R : ℕ) :
    ∃ N, ∀ n ≥ N, latticeBox a R ⊆ latticeBox (c n) (r n) := by
  classical
  let i := fun v => Classical.choose (hexhaust v)
  let N := (latticeBox a R).sup i
  refine ⟨N, fun n hn v hv => ?_⟩
  have hi : i v ≤ N := Finset.le_sup hv
  have hiv := Classical.choose_spec (hexhaust v)
  exact (latticeBox_subset_of_nested hnest (hi.trans hn)) hiv

/-- The canonical origin-centered boxes are nested. -/
theorem origin_latticeBox_nested (n : ℕ) :
    latticeBox (0, 0) n ⊆ latticeBox (0, 0) (n + 1) :=
  latticeBox_mono (0, 0) (Nat.le_succ n)

/-- Every lattice vertex lies in some canonical origin-centered box. -/
theorem origin_latticeBox_exhaustive (v : LatticeVertex) :
    ∃ n, v ∈ latticeBox (0, 0) n := by
  refine ⟨max v.1.natAbs v.2.natAbs, ?_⟩
  rw [mem_latticeBox]
  omega

open Filter Topology

/-- A common weak limit along every nested exhaustive sequence of boxes. -/
def WeakBoxLimit {X : Type*} [TopologicalSpace X] (law : LatticeVertex → ℕ → X) (μ : X) : Prop :=
  ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
    (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
    (∀ v, ∃ n, v ∈ latticeBox (c n) (r n)) →
    Tendsto (fun n => law (c n) (r n)) atTop (𝓝 μ)

theorem WeakBoxLimit.atOrigin {X : Type*} [TopologicalSpace X] {law : LatticeVertex → ℕ → X}
    {μ : X} (h : WeakBoxLimit law μ) : Tendsto (law (0, 0)) atTop (𝓝 μ) :=
  h _ id origin_latticeBox_nested origin_latticeBox_exhaustive

/-- Comparison on a continuous, injective system of ordered coordinates makes
weak box limits independent of the nested exhaustive sequence. -/
theorem boxLimit_existsUnique_of_compare {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [PartialOrder Y] [TopologicalSpace Y] [OrderClosedTopology Y]
    (law : LatticeVertex → ℕ → X) (κ : X → Y) (hc : Continuous κ) (hi : Function.Injective κ)
    (hcompare : ∀ a b r s, latticeBox a r ⊆ latticeBox b s → κ (law a r) ≤ κ (law b s))
    (hconv : ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
      (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
      ∃ μ, Tendsto (fun n => law (c n) (r n)) atTop (𝓝 μ)) :
    ∃! μ, WeakBoxLimit law μ := by
  have hle {c d : ℕ → LatticeVertex} {r s : ℕ → ℕ} {μ ν : X}
      (hμ : Tendsto (fun n => law (c n) (r n)) atTop (𝓝 μ))
      (hν : Tendsto (fun n => law (d n) (s n)) atTop (𝓝 ν))
      (hn : ∀ n, latticeBox (d n) (s n) ⊆ latticeBox (d (n + 1)) (s (n + 1)))
      (he : ∀ v, ∃ n, v ∈ latticeBox (d n) (s n)) : κ μ ≤ κ ν := by
    refine le_of_tendsto' ((hc.tendsto μ).comp hμ) fun j => ?_
    obtain ⟨K, hK⟩ := latticeBox_subset_eventually_of_nested_exhaustive hn he (c j) (r j)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((hc.tendsto ν).comp hν)
      (eventually_atTop.2 ⟨K, fun k hk => hcompare _ _ _ _ (hK k hk)⟩)
  obtain ⟨μ, hμ⟩ := hconv (fun _ => (0, 0)) id origin_latticeBox_nested
  refine ⟨μ, ?_, fun _ hν => tendsto_nhds_unique
    hν.atOrigin hμ⟩
  intro c r hn he
  obtain ⟨ν, hν⟩ := hconv c r hn
  have e := hi (le_antisymm (hle hν hμ origin_latticeBox_nested origin_latticeBox_exhaustive)
    (hle hμ hν hn he))
  exact e ▸ hν

end PottsDiscontinuity.FK
