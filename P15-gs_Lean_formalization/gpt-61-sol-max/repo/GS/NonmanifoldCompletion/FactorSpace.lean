import GS.MatrixGeometry.BlockGroup

import GS.NonmanifoldCompletion.BlockExtraction




/-!
# A compact parameter space whose image is exactly the original localFamily

This uses all orthogonal block factors, not a selected normal-form branch.
The equivalence with the scalar-shuffle definition is proved by extraction.

-/
noncomputable section
namespace GS.NonmanifoldCompletion

/-- The order is (left outer blocks, first middle block, second middle block,
right outer blocks). It matches the finite compact product used below. -/
abbrev SmallBlockParameters (q : ℕ) :=
  (Fin q → Mat 2) × Mat q × Mat q × (Fin q → Mat 2)

def smallFactorSet (q : ℕ) : Set (SmallBlockParameters q) :=
  {p | (∀ i, Orthogonal (p.1 i)) ∧ Orthogonal p.2.1 ∧ Orthogonal p.2.2.1 ∧
    (∀ j, Orthogonal (p.2.2.2 j))}

def smallFactorMap (p : SmallBlockParameters q) := flattenBlocks (blockMatrix p.1 * centralPair p.2.1 p.2.2.1 * blockMatrix p.2.2.2)

theorem continuous_smallFactorMap (q : ℕ) : Continuous (@smallFactorMap q) := by
  fun_prop [smallFactorMap, flattenBlocks, pullMatrix, centralPair]

theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) := by
  have hc (m : ℕ) : IsCompact {A : Mat m | Orthogonal A} := by
    simpa [GS.MatrixBase.CSupported, GS.MatrixBase.Unitary, Orthogonal] using
      GS.MatrixBase.compact_blockU_set (𝕜 := ℝ) (fun _ : Fin m => 0)
  have houter : IsCompact {U : Fin q → Mat 2 | ∀ i, Orthogonal (U i)} :=
    isCompact_pi_infinite (fun _ => hc 2)
  exact houter.prod ((hc q).prod ((hc q).prod houter))

/-- Crucially, this is the FULL GS image, not the small originalF image. -/
theorem image_smallFactorMap (q : ℕ) :
    (@smallFactorMap q) '' smallFactorSet q = localFamily q := by
  ext M
  constructor
  · rintro ⟨⟨U,A,B,V⟩,⟨hU,hA,hB,hV⟩,rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB
  · intro hM
    obtain ⟨U,V,A,B,hU,hV,hA,hB,he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
    exact ⟨(U,A,B,V),⟨hU,hA,hB,hV⟩,he.symm⟩

end GS.NonmanifoldCompletion
