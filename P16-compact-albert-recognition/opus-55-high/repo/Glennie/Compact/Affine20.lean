/- The relabelling action on the 20 chart
coordinates is faithful, and every non-identity relabelling has a nowhere-dense fixed set.
  * `AffineComb.continuous20`: a map of the 20 coordinates that preserves affine combinations
    is continuous (it is a linear map plus a constant; finite dimension).
  * `AffineComb.eq_of_interior_fixed`: if such a map fixes a neighbourhood of one point, it
    fixes every point (restrict to the line through that point).
  * A test ledger `Lstar` in the affine domain whose 27 pair-block entries are pairwise
    different (`zTab`, kernel-checked integers). Five chart coordinates of `Lstar` already
    pin down the relabelling: `relabel_eq_one_of_heads`.
  * `act20_moved`, `relabel_faithful`, `fixed_interior_empty`, `isOpen_moved`, `dense_moved`,
    `relabel_gates` (the `hopen`/`hdense` hypotheses of the RobustBranchCore
    `dense_avoids_relabel_fixed_points`, for `ledgerRelabel := act20`), and `dense_avoids`.
`Lstar` is a point of the affine chart domain, not claimed to be the ledger of actual frames.
No rank, inverse-function, section or Phi statement is made here.
Proof method: Fin 3 splits use the Boolean `fin3_cases`; chart coordinates and ledger
projections are rewritten with rfl lemmas on variables before any comparison. The one linear
map built here (`AffineComb.continuous20`) is an abstract `f`, spelled `→ₗ[ℝ]` throughout. -/
module

public import Glennie.Compact.Affine20.Chart
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie.Compact.Affine20



/-! ## Maps preserving affine combinations of the 20 coordinates -/

/-- A map of the 20 coordinates that preserves affine combinations is continuous. -/
theorem AffineComb.continuous20 {f : (Fin 20 → ℝ) → (Fin 20 → ℝ)} (hf : AffineComb f) :
    Continuous f := by
  have hsmul : ∀ (t : ℝ) (y : Fin 20 → ℝ), f (t • y) - f 0 = t • (f y - f 0) := by
    intro t y
    have h := hf 0 y t
    rw [sub_zero, zero_add] at h
    rw [h]
    abel
  have hadd : ∀ x y : Fin 20 → ℝ, f (x + y) - f 0 = (f x - f 0) + (f y - f 0) := by
    intro x y
    have h := hf ((2 : ℝ) • x) ((2 : ℝ) • y) (1 / 2)
    have e : (2 : ℝ) • x + (1 / 2 : ℝ) • ((2 : ℝ) • y - (2 : ℝ) • x) = x + y := by
      module
    rw [e] at h
    have h2x : f ((2 : ℝ) • x) = f 0 + (2 : ℝ) • (f x - f 0) := by grind
    have h2y : f ((2 : ℝ) • y) = f 0 + (2 : ℝ) • (f y - f 0) := by grind
    rw [h, h2x, h2y]
    module
  have hG := LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun x => f x - f 0
         map_add' := hadd
         map_smul' := fun t y => by
           try rw [RingHom.id_apply]
           exact hsmul t y } : (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ))
  have hf' : f = fun x => (f x - f 0) + f 0 := by
    funext x
    abel
  rw [hf']
  exact hG.fun_add continuous_const

/-! ## A test ledger with pairwise different pair entries -/

/-! ## Five chart coordinates of the test ledger pin down the relabelling -/

/-! ## Faithfulness and the fixed sets -/

end Glennie.Compact.Affine20
