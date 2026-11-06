module

public import NearlyMinimax.HistoryPrefixHeap
public import NearlyMinimax.HistoryAppendMeasurable
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-!
# Exact marked density after deleting the appended maximal occurrence
-/

𝚯
𝚨

𝚲

𝗇 𝔄 𝘨₂
@[simp] theorem historyFiniteMarkAppendEquiv_old (n : ℕ) [MeasurableSpace E]
    (fresh : E) marks x :
    historyFiniteMarkAppendEquiv n 𝔄 x.castSucc = marks x := by
  have hh := congrArg (fun p => p.2 x)
    $ (MeasurableEquiv.piFinSuccAbove 𝚓 $ Fin.last n ).apply_symm_apply 𝔄
  change historyFiniteMarkAppendEquiv n 𝔄 ((Fin.last n).succAbove x) = marks x at hh
  simp_all

𝗇 𝔅 𝘼
𝗇 𝔇 𝖴
𝗇 𝔈 Fin.cast 𝚈₂ x.position
𝗃 𝔊 ἀ dependent hsymm j g
/-- Every old occurrence in the canonical append carries exactly its original mark. -/
theorem historyCanonicalMarkAppendEquiv_old (dependent : 𝙁)
    (hsymm : 𝔅)
    j (g : HistoryShape 𝔇) [MeasurableSpace E]
    (fresh : E) marks
    x :
    𝔊 historyCanonicalMarkAppendEquiv 𝔄
      (Fin.cast (historyShapeLength_out dependent $ 𝗡₁ g ).symm
        (𝔊 historyCanonicalAppendHeapIso
          $ historyPrefixHeapEmbedding g.out dependent j x ).position) =
      marks 𝔈 := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    𝔊 historyCanonicalAppendCoordinates
    (β := 𝚓) (historyFiniteMarkAppendEquiv _ 𝔄)
    (𝔈).castSucc
  aesop

𝗇 𝔉 historyMarkedPieceWeight dependent a ⟨𝗡₁ g, 𝔊 historyCanonicalMarkAppendEquiv 𝔄⟩
/-- The source deleted polynomial equals the original marked density, with no deletion-density premise. -/
theorem historyCanonicalAppend_density_delete (dependent : 𝙁)
    (hsymm : 𝔅)
    j (g : HistoryShape 𝔇) [MeasurableSpace E]
    (fresh : E) marks
    a ρ t :
    historyScaledUpperDensity
      𝔉
      ρ (Finset.univ.erase 𝔊 historyCanonicalAppendedPiece) t =
      𝘡₂ t a 𝗬 := by
  classical
  let e := 𝔊 historyCanonicalAppendHeapIso
  let w := 𝔉
  have ht := historyScaledUpperDensity_orderIso_map e w ρ
    (Finset.univ.erase $ wordHeapAppendedPiece g.out dependent j ) t
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have hw : (w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j =
      historyMarkedPieceWeight dependent a 𝗬 := by
    funext x
    exact congrArg a $ 𝔊 historyCanonicalMarkAppendEquiv_old fresh marks x
  rw [historyPrefixHeap_density_delete, hw] at ht
  exact ht
