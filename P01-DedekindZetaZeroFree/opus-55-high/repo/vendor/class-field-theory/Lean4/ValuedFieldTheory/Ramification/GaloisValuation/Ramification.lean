module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import Mathlib.Data.Rat.Lemmas

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace RamificationTheory

open LocalFieldTheory

/-!
# Ramification filtrations

This file provides the group-theoretic lower ramification APIs used by local CFT.
Concrete valued extensions supply the action quotient estimates; the subgroup
and normality/antitonicity consequences are proved here.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace AntitoneNormalSubgroupFiltration
end AntitoneNormalSubgroupFiltration

/-- A depth function whose threshold subgroups form a lower ramification filtration. -/
structure LowerRamificationDepth (G : Type u) [Group G] where
  /-- The lower ramification depth of each group element. -/
  depth : G → WithTop ℕ
  /-- The identity has infinite ramification depth. -/
  depth_one : depth 1 = ⊤
  /-- Each depth threshold is closed under multiplication. -/
  depth_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth τ →
      (n : WithTop ℕ) ≤ depth (σ * τ)
  /-- Each depth threshold is closed under inversion. -/
  depth_inv_mem :
    ∀ {n : ℕ} {σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth σ⁻¹
  /-- Each depth threshold is preserved under conjugation. -/
  depth_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth (γ * σ * γ⁻¹)

namespace LowerRamificationDepth
end LowerRamificationDepth

/-- A ramification filtration coming from an action quotient tested against
principal units. -/
structure ValuationActionRamification (G : Type u) [Group G]
    (K : Type v) [Group K] where
  /-- The principal-unit filtration used to test action quotients. -/
  principalUnits : LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration K
  /-- The action of `G` on `K` by multiplicative automorphisms. -/
  action : G →* MulAut K
  /-- The element of `K` on which action quotients are evaluated. -/
  probe : K
  /-- Membership of action quotients at a fixed level is closed under multiplication. -/
  quotient_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action τ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (σ * τ)) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is closed under inversion. -/
  quotient_inv_mem :
    ∀ {n : ℕ} {σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action σ⁻¹) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is preserved under conjugation. -/
  quotient_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (γ * σ * γ⁻¹)) probe / probe) ∈ principalUnits.subgroup n

namespace ValuationActionRamification
