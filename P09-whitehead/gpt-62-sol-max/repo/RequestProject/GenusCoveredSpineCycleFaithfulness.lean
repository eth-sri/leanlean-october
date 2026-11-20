module

public import RequestProject.GenusCollapseCoverHomology
public import RequestProject.OrderNervePositiveFillings

@[expose] public section

/-! A covered two-dimensional spine has no nonzero two-chain bounding in its block. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_covered_spine_three_flags_empty (hf : IsPosetCover f) :
    IsEmpty (StrictOrdTet {p : P // f p ∈ genusSpineCellSet q}) :=
  strictOrdTet_isEmpty_of_rank (fun p => truncatedCellDimension (f p.1))
    (fun _ _ h => truncatedCellDimension_strictMono (hf.strictMono h))
    (fun p => genusSpineCell_dimension_le_two q ⟨f p.1, p.2⟩)

/-- A filling in the entire covering block is reflected to its actual spine;
normalization then makes it zero because that spine has no three-flags.
The input is an actual boundary, with no asphericity or relative-homology premise. -/
theorem genus_covered_spine_chain_zero_of_boundary (hf : IsPosetCover f)
    (c : StrictOrdTri {p : P // f p ∈ genusSpineCellSet q} →₀ ℤ)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y =
      cmap (Subtype.val : {p : P // f p ∈ genusSpineCellSet q} → P)
        (ordNerveChain2 (ordStrictInclusion2 c))) : c = 0 := by
  let B := fun p  => f p ∈ genusSpineCellSet q
  let z := ordNerveChain2 (ordStrictInclusion2 c)
  have hz : z ∈ Inc {p : P // B p} := ordNerveChain2_mem_inc _
  have hd : lengthProjection 3 (cmap Subtype.val z) =
      cmap Subtype.val z := by
    rw [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hbound' : ∃ y ∈ IncOn (fun _  => True), Nerve.bdry y = cmap Subtype.val z := by
    obtain ⟨y, hy, hdy⟩ := hbound
    refine ⟨y, ?_, hdy⟩
    simpa only [cmap_id] using
      cmap_mem_incOn_of_maps (f := id) monotone_id (fun _ => True.intro) hy
  obtain ⟨y, hy, hdy⟩ := (genusSpine_cover_homology q hf).2
    _ (cmap_val_mem_incOn B hz) hd hbound'
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn B hy
  have hdb : Nerve.bdry b = z := by
    apply cmap_val_injective B
    rw [cmap_bdry, hby]
    exact hdy
  have he : ordBoundary3 (decodeOrdNerve3 b) = ordStrictInclusion2 c := by
    apply ordNerveChain2_injective
    rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hb,
      ← lengthProjection_bdry, hdb, ordNerveChain2_lengthProjection]
  haveI := genus_covered_spine_three_flags_empty q hf
  have hn := congrArg normalizeOrdChain2 he
  rw [normalizeOrdBoundary3_eq_zero] at hn
  have hi  := normalizeOrdChain2_inclusion c
  exact (hn.trans hi).symm

end FiniteChains.Davis.Genus
