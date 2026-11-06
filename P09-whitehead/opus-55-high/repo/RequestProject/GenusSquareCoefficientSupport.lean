import RequestProject.GenusPositiveSquareCoefficients
import RequestProject.OrderNormalizationSupport


/-! Recovered square coefficients occur only on actual surviving ordinary spine faces. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineFace_top_dimension_two (f : (markedSpineCx q).F) :
    truncatedCellDimension f.1.1.2.2.1 = 2 := by
  have h01 := genusSpineCellDimension_strictMono q f.1.2.1
  have h12 := genusSpineCellDimension_strictMono q f.1.2.2
  change truncatedCellDimension f.1.1.1.1 < truncatedCellDimension f.1.1.2.1.1 at h01
  change truncatedCellDimension f.1.1.2.1.1 < truncatedCellDimension f.1.1.2.2.1 at h12
  have hmax := genusSpineCell_dimension_le_two q f.1.1.2.2
  omega

/-- Every genuine two-flag of the surviving spine ends at an ordinary retained square,
not at a cut cell (all cut triangles were removed). -/
theorem markedSpineFace_top_old (f : (markedSpineCx q).F) :
    ∃ a, f.1.1.2.2.1 = Sum.inl a := by
  have hd := markedSpineFace_top_dimension_two q f
  cases hc : f.1.1.2.2.1 with
  | inl a => simp
  | inr σ =>
      have hs := f.1.1.2.2.2
      rw [hc] at hs
      have hcard := genusSpine_cut_card_le_two q σ hs
      rw [hc] at hd
      change σ.1.card - 1 = 2 at hd
      omega

/-- A nonzero recovered square coefficient comes from an actual ordinary two-cell
surviving the chosen genus collapse. -/
theorem markedSpine_square_coefficient_support d
    s
    (hs : qSquareCycleCoefficients
      (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)) s ≠ 0) :
    ∃ a,
      (Sum.inl a) ∈ genusSpineCellSet q ∧ a.1 = s.1 := by
  classical
  obtain ⟨t, ht, he⟩ := normalizeOrdChain2_support _ _ (Finsupp.mem_support_iff.mpr hs)
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  have htop := congrArg (·.2.2) he
  rw [← hf] at htop
  cases' markedSpineFace_top_old q f with a ha
  have hmem := f.1.1.2.2.2
  rw [ha] at hmem
  refine ⟨a, hmem, ?_⟩
  change (genusSpineCellToOld q f.1.1.2.2).1 = s.1 at htop
  simpa [genusSpineCellToOld, truncatedCellRetraction, ha] using htop
