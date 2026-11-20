module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.Herbrand.Function
public import ValuedFieldTheory.Ramification.Herbrand.Tower

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The fibre average in Herbrand's theorem

This file formalizes the remaining finite-group calculation in
the Herbrand quotient theorem.  For a normal subgroup `H`, the depth on `G`
defines the lower filtration

`H_s = {τ : H | s + 1 ≤ depth τ}`.

For a nonidentity class in `G ⧸ H`, all depths in its fibre are finite, so
their normalized average is a definition rather than an assumed quotient
depth.  The main theorem identifies this average, at a representative of
maximal depth, with the Herbrand function of the above filtration.  The
valued-field equality between this average and the actual quotient depth is
the separate input of the quotient-depth identity.
-/

noncomputable section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace HerbrandGroupTheory
namespace NonarchimedeanDepth

variable {G : Type u} [Group G]

variable (D : NonarchimedeanDepth G)

/-- States the theorem `depth_inv`. -/
theorem depth_inv (σ : G) : D.depth σ⁻¹ = D.depth σ := by
  by_contra h
  have htop : min (D.depth σ⁻¹) (D.depth σ) = ⊤ := by
    rw [← (D.depth_mul_eq_min_of_ne h)]
    simp [D.depth_one]
  exact h (((min_eq_top.mp htop).1).trans ((min_eq_top.mp htop).2).symm)

variable (H : Subgroup G) [H.Normal]

noncomputable local instance averageSubgroupFintype [Finite G] : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance averageQuotientFiberFintype [Finite G] (q : G ⧸ H) :
    Fintype (QuotientFiber H q) :=
  Fintype.ofFinite (QuotientFiber H q)

/-- The `n`th lower group of `H` cut out by the ambient depth:
`H_n = {τ | n + 1 ≤ depth τ}`. -/
def depthLowerSubgroup (n : ℕ) : Subgroup H where
  carrier := {τ | WithTop.some (n + 1) ≤ D.depth (τ : G)}
  one_mem' := by simp [D.depth_one]
  mul_mem' := by
    intro σ τ hσ hτ
    exact le_trans (le_min hσ hτ) (D.depth_mul_ge_min (σ : G) (τ : G))
  inv_mem' := by
    intro σ hσ
    simpa [D.depth_inv] using hσ

omit [H.Normal] in
/-- States the theorem `mem_depthLowerSubgroup_iff`. -/
@[simp] theorem mem_depthLowerSubgroup_iff (n : ℕ) (τ : H) :
    τ ∈ D.depthLowerSubgroup H n ↔
      WithTop.some (n + 1) ≤ D.depth (τ : G) :=
  Iff.rfl

/-- The exact lower filtration on `H` induced by `D`.  Conjugation
invariance of the depth supplies normality of every level. -/
def depthLowerFiltration : AntitoneNormalSubgroupFiltration H where
  lower := D.depthLowerSubgroup H
  lower_normal := by
    intro n
    constructor
    intro τ hτ σ
    change WithTop.some (n + 1) ≤ D.depth (((σ * τ * σ⁻¹ : H) : G))
    rw [show (((σ * τ * σ⁻¹ : H) : G)) =
        (σ : G) * (τ : G) * (σ : G)⁻¹ by rfl, D.depth_conj]
    exact hτ
  antitone := fun {m n} hmn τ hτ => by
    exact le_trans (WithTop.coe_le_coe.2 (Nat.add_le_add_right hmn 1)) hτ

omit [H.Normal] in
/-- States the theorem `depthLowerFiltration_lower`. -/
@[simp] theorem depthLowerFiltration_lower (n : ℕ) :
    (D.depthLowerFiltration H).lower n = D.depthLowerSubgroup H n :=
  rfl

end NonarchimedeanDepth
end HerbrandGroupTheory
end RamificationTheory.DiscreteValuationField

end
