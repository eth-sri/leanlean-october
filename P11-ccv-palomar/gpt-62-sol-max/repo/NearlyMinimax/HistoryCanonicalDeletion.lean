module

public import NearlyMinimax.HistoryPrefixHeap
public import NearlyMinimax.HistoryAppendMeasurable


@[expose] public section

/-!
# Exact marked density after deleting the appended maximal occurrence
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

@[simp] theorem historyFiniteMarkAppendEquiv_old (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) (x : Fin n) :
    historyFiniteMarkAppendEquiv n (fresh, marks) x.castSucc = marks x := by
  simp_all [historyFiniteMarkAppendEquiv]

section
variable (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))

/-- Actual prefix occurrences have the old mark coordinates in the canonical append. -/
theorem historyCanonicalAppendCoordinates_old
    (x : WordHeapPiece g.out dependent) :
    historyCanonicalAppendCoordinates dependent hsymm j g
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
      Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendHeapIso dependent hsymm j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position := by
  rfl

section
variable {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E)

/-- Every old occurrence in the canonical append carries exactly its original mark. -/
theorem historyCanonicalMarkAppendEquiv_old
    (x : WordHeapPiece g.out dependent) :
    historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendHeapIso dependent hsymm j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position) =
      marks (Fin.cast (historyShapeLength_out dependent g).symm x.position) := by
  rw [← historyCanonicalAppendCoordinates_old]
  simp

/-- The source deleted polynomial equals the original marked density, with no deletion-density premise. -/
theorem historyCanonicalAppend_density_delete
    (a : E → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity
      (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
      ρ (Finset.univ.erase (historyCanonicalAppendedPiece dependent hsymm j g)) t =
      historyMarkedDensity dependent ρ t a ⟨g, marks⟩ := by
  classical
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  let w := historyMarkedPieceWeight dependent a
    ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩
  have ht := historyScaledUpperDensity_orderIso_map e w ρ
    (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have hw : (w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j =
      historyMarkedPieceWeight dependent a ⟨g, marks⟩ := by
    funext x
    exact congrArg a (historyCanonicalMarkAppendEquiv_old dependent hsymm j g fresh marks x)
  rw [historyPrefixHeap_density_delete, hw] at ht
  exact ht

end

end

end NearlyMinimax
