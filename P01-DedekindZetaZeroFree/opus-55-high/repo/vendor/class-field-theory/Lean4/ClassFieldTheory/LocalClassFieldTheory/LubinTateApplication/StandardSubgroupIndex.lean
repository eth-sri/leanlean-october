module

public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
public import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
public import ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The canonical standard subgroup index

For the topology-first nonarchimedean local field `K`, the canonical
Lubin--Tate uniformizer and the `(n + 1)`-st principal units generate a
subgroup of `Kˣ` of index

`(Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n`.

The proof passes from field units to integer units, transports the latter
through the canonical packaged local-field equivalence, and then uses the
finite standard Lubin--Tate unit-parameter count.
-/


open scoped ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A finite-index subgroup contained in another subgroup with the same
index is already equal to it.  The nonzero-index hypothesis excludes the
infinite-index convention `index = 0`. -/
theorem subgroup_eq_of_le_of_index_eq_of_ne_zero
    {G : Type*} [Group G] {H N : Subgroup G}
    (hHN : H ≤ N) (hindex : H.index = N.index)
    (hindex_ne : H.index ≠ 0) :
    H = N := by
  let _ : H.FiniteIndex := ⟨hindex_ne⟩
  apply le_antisymm hHN
  by_contra hNH
  have hne : H ≠ N := by
    intro heq
    apply hNH
    rw [heq]
  have hstrict : H < N := lt_of_le_of_ne hHN hne
  have hi := Subgroup.index_strictAnti hstrict
  simp_all
