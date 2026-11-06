import Mathlib.Tactic

import GS.UnitaryNonmanifold.ScalarBridge
import GS.UnitaryManifold.BlockGroup



/-!
# Compact full factor space for the unitary three-factor family

The parameter space contains all unitary outer and middle blocks. Its image
is exactly the original scalar-shuffle family, including degenerate blocks.
-/

noncomputable section
open GS.UnitaryNonmanifold

namespace GS.UnitaryLocalModel

variable (q n : ℕ)

/-- Parameters are ordered as left blocks, two middle blocks, and right blocks. -/
abbrev SmallBlockParameters  :=
  (Fin q → CMat 2) × CMat q × CMat q × (Fin q → CMat 2)

def smallFactorSet  : Set (SmallBlockParameters q) :=
  {p | (∀ i, GS.Unitary (p.1 i)) ∧ GS.Unitary p.2.1 ∧ GS.Unitary p.2.2.1 ∧
    (∀ j, GS.Unitary (p.2.2.2 j))}

def smallFactorMap {q : ℕ} (p : SmallBlockParameters q) := flattenBlocks (GS.UnitaryNonmanifold.blockMatrix p.1 * centralPair p.2.1 p.2.2.1 *
    GS.UnitaryNonmanifold.blockMatrix p.2.2.2)

theorem smallFactorMap_block {q : ℕ} (p : SmallBlockParameters q)
    (i j : Fin q) (a b : Fin 2) :
    smallFactorMap p (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      (p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j) a b := by
  rw [smallFactorMap,flattenBlocks_apply,small_block_sandwich]
  rfl

theorem continuous_smallFactorMap  : Continuous (@smallFactorMap q) := by
  fun_prop [smallFactorMap, flattenBlocks, pullMatrix, centralPair]

theorem isCompact_unitary_set  : IsCompact {A : CMat n | GS.Unitary A} := by
  simpa [GS.MatrixBase.CSupported, GS.MatrixBase.Unitary, GS.Unitary] using
    GS.UnitaryManifold.compact_blockU_set  (fun _ : Fin n => 0)

theorem isCompact_smallFactorSet  : IsCompact (smallFactorSet q) := by
  have houter : IsCompact {U : Fin q → CMat 2 | ∀ i, GS.Unitary (U i)} :=
    isCompact_pi_infinite (fun _ => isCompact_unitary_set 2)
  exact houter.prod ((isCompact_unitary_set q).prod ((isCompact_unitary_set q).prod houter))

/-- Every original factorization is retained in this compact parameter space. -/
theorem image_smallFactorMap  :
    (@smallFactorMap q) '' smallFactorSet q = GS.UnitaryNonmanifold.localFamily q := by
  ext M
  constructor
  · rintro ⟨⟨U,A,B,V⟩,⟨hU,hA,hB,hV⟩,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB
  · intro hM
    obtain ⟨U,V,A,B,hU,hV,hA,hB,he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
    exact ⟨(U,A,B,V),⟨hU,hA,hB,hV⟩,he.symm⟩

/-- The corresponding compact subtype, for results stated using CompactSpace. -/
abbrev SmallFactorSpace  := {p : SmallBlockParameters q // p ∈ smallFactorSet q}

instance smallFactorSpace_compactSpace (q : ℕ) : CompactSpace (SmallFactorSpace q) :=
  isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)

def smallFactorValue  (p : SmallFactorSpace q) : CMat (q*2) :=
  smallFactorMap p.val

theorem continuous_smallFactorValue  : Continuous (smallFactorValue q) :=
  (continuous_smallFactorMap q).comp continuous_subtype_val

theorem range_smallFactorValue  :
    Set.range (smallFactorValue q) = GS.UnitaryNonmanifold.localFamily q := by
  rw [← image_smallFactorMap]
  ext M
  constructor
  · aesop
  · aesop

end GS.UnitaryLocalModel
