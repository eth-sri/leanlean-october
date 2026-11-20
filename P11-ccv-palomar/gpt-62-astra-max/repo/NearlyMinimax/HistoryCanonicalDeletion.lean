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
  have hh := congrArg (fun p => p.2 x)
    ((MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  change historyFiniteMarkAppendEquiv n (fresh, marks) ((Fin.last n).succAbove x) = _ at hh
  simpa only [Fin.succAbove_last_apply] using hh

variable {dependent : J → J → Prop} [Std.Symm dependent] (j : J) {g : DependenceHeap dependent}
    {E : Type*} [MeasurableSpace E] (fresh : E) (marks : Fin (historyShapeLength g) → E)

/-- Every old occurrence in the canonical append carries exactly its original mark. -/
theorem historyCanonicalMarkAppendEquiv_old
    (x : WordHeapPiece g.out dependent) :
    historyCanonicalMarkAppendEquiv j g (fresh, marks)
      (Fin.cast (historyShapeLength_out (historyShapeAppend j g)).symm
        (historyCanonicalAppendHeapIso j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position) =
      marks (Fin.cast (historyShapeLength_out g).symm x.position) := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    (historyCanonicalAppendCoordinates j g)
    (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (Fin.cast (historyShapeLength_out g).symm x.position).castSucc
  change MeasurableEquiv.piCongrLeft
    (fun _ => E)
    (historyCanonicalAppendCoordinates j g)
    (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (historyCanonicalAppendCoordinates j g
      (Fin.cast (historyShapeLength_out g).symm x.position).castSucc) = _
  rw [hh, historyFiniteMarkAppendEquiv_old]

/-- The source deleted polynomial equals the original marked density, with no deletion-density premise. -/
theorem historyCanonicalAppend_density_delete
    (a : E → ℝ) (ρ t : ℝ) :
    let pieceWeight := historyMarkedPieceWeight dependent a ⟨historyShapeAppend j g, historyCanonicalMarkAppendEquiv j g (fresh, marks)⟩
    historyScaledUpperDensity
      (pieceWeight)
      ρ (Finset.univ.erase (historyCanonicalAppendedPiece j g)) t =
      historyMarkedDensity ρ t a ⟨g, marks⟩ := by
  intro pieceWeight
  classical
  let e := historyCanonicalAppendHeapIso j g
  let w := pieceWeight
  have ht := historyScaledUpperDensity_orderIso_map e w ρ
    (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have hw : (w ∘ e) ∘ historyPrefixHeapEmbedding .. =
      historyMarkedPieceWeight dependent a ⟨g, marks⟩ := by
    funext x
    exact congrArg a (historyCanonicalMarkAppendEquiv_old j fresh marks x)
  rw [historyPrefixHeap_density_delete, hw] at ht
  exact ht

end NearlyMinimax
