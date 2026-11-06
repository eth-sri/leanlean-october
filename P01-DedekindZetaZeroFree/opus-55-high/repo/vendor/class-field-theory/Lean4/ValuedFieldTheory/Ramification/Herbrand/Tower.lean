module

public import ValuedFieldTheory.Ramification.GaloisValuation.Ramification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Finite-group sources for Herbrand's theorem

This file isolates the part of the Herbrand quotient theorem which is
independent of valuations.  A discrete nonarchimedean depth has the two
properties of `i(σ) = v(σ(a) - a)` used in the ramification-depth proof: multiplication
does not decrease the minimum depth, and it is exactly the minimum when the
two depths differ.

For a finite group modulo a normal subgroup, every nontrivial quotient fibre
has a representative of maximal (finite) depth.  The main result below proves
the identity

`i(σ τ) = min (i(σ), i(τ))`

for such a representative `σ` and every `τ` in the normal subgroup.  The
remaining valued-field input for the Herbrand quotient theorem is the quotient-depth identity: the depth
on the quotient is the normalized sum of the depths in this fibre.  That
input is deliberately not packaged here as a hypothesis or data field.
-/

noncomputable section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace HerbrandGroupTheory

variable {G : Type u} [Group G]

/-- The purely group-theoretic laws of the discrete depth used in the proof
of Herbrand's theorem.  The value `⊤` occurs exactly at the identity. -/
structure NonarchimedeanDepth (G : Type u) [Group G] where
  /-- The discrete nonarchimedean depth of each group element. -/
  depth : G → WithTop ℕ
  /-- An element has infinite depth exactly when it is the identity. -/
  depth_eq_top_iff : ∀ σ, depth σ = ⊤ ↔ σ = 1
  /-- The depth of a product is at least the minimum depth of its factors. -/
  depth_mul_ge_min : ∀ σ τ, min (depth σ) (depth τ) ≤ depth (σ * τ)
  /-- Factors of unequal depth give a product whose depth is their minimum. -/
  depth_mul_eq_min_of_ne :
    ∀ {σ τ}, depth σ ≠ depth τ → depth (σ * τ) = min (depth σ) (depth τ)
  /-- Depth is invariant under conjugation. -/
  depth_conj : ∀ γ σ, depth (γ * σ * γ⁻¹) = depth σ

namespace NonarchimedeanDepth
