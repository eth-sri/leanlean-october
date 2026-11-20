module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.KMap
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Definitions for the asymptotics of discrete Bethe roots

This module records the objects in (2.3) and (2.5) of
arXiv:1611.09877v2.  The step density is extended by zero off its cyclic root
partition.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- Weighted absolute errors on the compact angular interval. -/
noncomputable abbrev densityValues (Δ : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  range fun α : Icc (-Real.pi) Real.pi => |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|

/-- The weighted supremum norm (2.3), in the angular coordinate. -/
noncomputable def densityNorm (Δ : ℝ) (f : ℝ → ℝ) : ℝ := sSup (densityValues Δ f)

/-- Cyclic extension of an ordered root vector, with the two extra endpoints
`p₀ = pₙ - 2π` and `pₙ₊₁ = p₁ + 2π`. -/
noncomputable def rootPartitionPoint (n : ℕ) (p : Fin n → ℝ) (hn : 0 < n)
    (j : Fin (n + 2)) : ℝ :=
  if h0 : j.val = 0 then
    p ⟨n - 1, by omega⟩ - 2 * Real.pi
  else if hn₁ : j.val = n + 1 then
    p ⟨0, by omega⟩ + 2 * Real.pi
  else
    p ⟨j.val - 1, by omega⟩

/-- Multiplicity of the `j`th root gap in (2.5): interior gaps have weight 1,
and the two cyclic boundary gaps have weight `N + 1 - 2n` (equal to `2r+1`
when `n=N/2-r`). -/
def rootGapMultiplicity (N n : ℕ) (j : Fin (n + 1)) : ℝ :=
  if j.val = 0 ∨ j.val = n then ((N + 1 - 2 * n : ℕ) : ℝ) else 1

/-- The step density `ρ_p` of (2.5), on the cyclic root partition. -/
noncomputable def rootStepDensity (N n : ℕ) (p : Fin n → ℝ)
    (hn : 0 < n) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1),
    if rootPartitionPoint n p hn j.castSucc ≤ x ∧ x < rootPartitionPoint n p hn j.succ then
      rootGapMultiplicity N n j /
        ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
    else 0

/-- Error of the root step density relative to the limiting density. -/
noncomputable abbrev rootStepError (Δ : ℝ) (N : ℕ) {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) : ℝ → ℝ :=
  fun x => rootStepDensity N n p hn x - rho Δ x

section

variable {ι : Type*} (N : ι → ℕ)

/-- Size side condition `0 < N i / 2` for the root step densities of Theorem 2.9. Statements
use this named lemma instead of an inline tactic proof, so that no module-private auxiliary
proof appears in an exported statement. -/
theorem half_pos_of_half_sub_pos (r : ℕ) (hn : ∀ i, 0 < N i / 2 - r)
    (i : ι) :
    0 < N i / 2 := by
  have := hn i
  omega

/-- Size side condition `2 * (N i / 2) ≤ N i` for the root step densities of Theorem 2.9. -/
theorem two_mul_half_le (i : ι) : 2 * (N i / 2) ≤ N i := by
  omega

/-- Size side condition `2 * (N i / 2 - r) ≤ N i` for the root step densities of Theorem 2.9. -/
theorem two_mul_half_sub_le (r : ℕ) (i : ι) :
    2 * (N i / 2 - r) ≤ N i := by
  omega

end

end PottsDiscontinuity.Bethe
