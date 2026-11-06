import RequestProject.GenusCollapseCoverHomology
import RequestProject.OrderNervePositiveFillings
import RequestProject.Tac


/-! A covered two-dimensional spine has no nonzero two-chain bounding in its block. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_covered_spine_three_flags_empty (hf : IsPosetCover f) :
    IsEmpty (StrictOrdTet {p : P // f p ∈ genusSpineCellSet q}) := by
  refine ⟨fun t => ?_⟩
  have h01 := truncatedCellDimension_strictMono (hf.strictMono t.2.1)
  have h12 := truncatedCellDimension_strictMono (hf.strictMono t.2.2.1)
  have h23 := truncatedCellDimension_strictMono (hf.strictMono t.2.2.2)
  have hmax := genusSpineCell_dimension_le_two q ⟨f t.1.2.2.2.1, t.1.2.2.2.2⟩
  grind

/-- A filling in the entire covering block is reflected to its actual spine;
normalization then makes it zero because that spine has no three-flags.
The input is an actual boundary, with no asphericity or relative-homology premise. -/
theorem genus_covered_spine_chain_zero_of_boundary (hf : IsPosetCover f)
    c
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y =
      cmap (Subtype.val : {p : P // f p ∈ genusSpineCellSet q} → P)
        (ordNerveChain2 (ordStrictInclusion2 c))) : c = 0 := by
  let B := fun p => f p ∈ genusSpineCellSet q
  let z := ordNerveChain2 (ordStrictInclusion2 c)
  have hz : z ∈ Inc _ := ordNerveChain2_mem_inc _
  have hd : lengthProjection 3 (cmap Subtype.val z) =
      cmap Subtype.val z := by
    rw [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hbound' : ∃ y ∈ IncOn (fun _ => True), Nerve.bdry y = cmap Subtype.val z := by
    obtain ⟨y, hy, hdy⟩ := hbound
    refine ⟨y, ?_, hdy⟩
    simpa [cmap_id] using
      cmap_mem_incOn_of_maps (f := id) monotone_id (by simp) hy
  obtain ⟨y, hy, hdy⟩ := (genusSpine_cover_homology q hf).2
    _ (cmap_val_mem_incOn B hz) hd hbound'
  have hne : ∃ p : P, B p := by
    cases' hf.surj (spineBase q).1 with p hp
    grind
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn B hy
  have hdb : Nerve.bdry b = z := by
    apply cmap_val_injective B hne
    rw [cmap_bdry, hby]
    exact hdy
  have he : ordBoundary3 (decodeOrdNerve3 b) = ordStrictInclusion2 c := by
    apply ordNerveChain2_injective
    rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hb,
      ← lengthProjection_bdry, hdb, ordNerveChain2_lengthProjection]
  haveI := genus_covered_spine_three_flags_empty q hf
  have hzero : normalizeOrdChain3 (decodeOrdNerve3 b) = 0 := by
    ext t
    exact isEmptyElim t
  have hn := congrArg normalizeOrdChain2 he
  rw [normalizeOrdChain2_ordBoundary3, hzero, map_zero] at hn
  have hi : normalizeOrdChain2 (ordStrictInclusion2 c) = c := normalizeOrdChain2_inclusion c
  aesop
