module

public import RequestProject.GenusOldCoverSpineFaithfulness

@[expose] public section

/-!
Actual chain generation and reference-filling adjustment in every old-cell
cover. The cycle-generation hypothesis is supplied by the proved geometric
collapse of the truncated block, rather than assumed of the old cover.

Written proof terms; no verification has been run under the current workflow.
-/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

variable (hf : IsPosetCover f)
include hf

section

variable (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z) (hcyc : Nerve.bdry z = 0)
include hz hd hcyc

/-- Every homogeneous old-cover two-cycle is represented by an actual cycle on
the actual covered spine, modulo an actual increasing three-boundary. -/
theorem genus_old_cover_spine_nerve_generation :
    ∃ c ∈ Inc _, lengthProjection 3 c = c ∧
      Nerve.bdry c = 0 ∧ ∃ y ∈ Inc P,
        z = cmap (oldCoveredSpineToOld q f) c + Nerve.bdry y := by
  let B := fun p : TruncatedCover f => truncatedCoverProjection f p ∈ genusSpineCellSet q
  let r := truncatedCoverRetraction f
  let z' := cmap (truncatedCoverSection f) z
  have hz' : z' ∈ IncOn (fun _ : TruncatedCover f => True) :=
    cmap_mem_incOn_of_maps (truncatedCoverSection_monotone f hf.mono) (fun _ => True.intro) hz
  have hd' : lengthProjection 3 z' = z' := by
    rw [lengthProjection_cmap, hd]
  have hcyc' : Nerve.bdry z' = 0 := by
    erw [← cmap_bdry, hcyc, map_zero]
  obtain ⟨c₀, hc₀, y₀, hy₀, hcc₀, he₀⟩ :=
    (genusSpine_cover_homology q (truncatedCoverProjection_isPosetCover f hf)).1
      z' hz' hd' hcyc'
  let b := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hc₀
  have hbc : Nerve.bdry b = 0 := by
    erw [← lengthProjection_bdry, hcc₀, map_zero]
  have he : z' = b + Nerve.bdry y := by
    erw [← hd', he₀, map_add, lengthProjection_bdry]
  have hne : ∃ p : TruncatedCover f, B p := by
    obtain ⟨p, hp⟩ := (truncatedCoverProjection_isPosetCover f hf).surj (spineBase q).1
    refine ⟨p, ?_⟩
    change truncatedCoverProjection f p ∈ genusSpineCellSet q
    simp [hp]
  obtain ⟨c, hc, hcb⟩ := exists_preimage_of_mem_incOn B hb
  have hcd : lengthProjection 3 c = c := by
    apply cmap_val_injective B hne
    erw [← lengthProjection_cmap, hcb, (lengthProjection_idempotent _ _)]
  have hcc : Nerve.bdry c = 0 := by
    apply cmap_val_injective B hne
    simp [cmap_bdry, hcb, hbc, map_zero]
  refine ⟨c, hc, hcd, hcc, cmap r y, cmap_mem_inc_of_monotone (posetPullbackOriginal_monotone f truncatedCellRetraction) (lengthProjection_mem_inc _ (incOn_le_inc _ hy₀)), ?_⟩
  have hp := congrArg (cmap r) he
  have hreturn : cmap r z' = z := by
    erw [cmap_comp]
    apply cmap_id
  erw [hreturn, map_add, cmap_bdry, ← hcb, cmap_comp] at hp
  exact hp

/-- The preceding geometric representative can be made strictly cellular.
Degenerate flags are removed with the explicit normalization three-chain. -/
theorem genus_old_cover_spine_cycle_generation :
    ∃ c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0 ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 c)) + Nerve.bdry y := by
  obtain ⟨b, hb, hbd, hbc, y, hy, he⟩ :=
    genus_old_cover_spine_nerve_generation q f hf z hz hd hcyc
  let a := decodeOrdNerve2 b
  have ha : ordNerveChain2 a = b := by
    erw [ordNerveChain2_decode hb, hbd]
  have hac :=
    (ordNerveChain2_cycle_iff a).mp (by erw [ha] <;> assumption)
  let w := ordNerveChain3 (ordNormalizationHomotopy2 a)
  have hwb : b - ordNerveChain2 (ordStrictInclusion2 (normalizeOrdChain2 a)) =
      Nerve.bdry w := by
    erw [← ha]
    exact ordNerve_normalization_cycle a hac
  refine ⟨normalizeOrdChain2 a, normalizeOrdChain2_cycle a hac,
    cmap _ w + y, (Inc _).add_mem (cmap_mem_inc_of_monotone (oldCoveredSpineToOld_monotone q f) (ordNerveChain3_mem_inc _)) hy, ?_⟩
  erw [map_add, ← cmap_bdry, ← hwb, map_sub, he]
  abel

end

/-- Any spine filling can be adjusted by an actual spine cycle so that its
old-cover realization represents a prescribed geometric filling of the same
boundary. This is the normalization needed when choosing the marked reference
filling before arbitrary substitutions. -/
theorem genus_old_cover_spine_adjust_filling
    (d : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry (cmap (oldCoveredSpineToOld q f)
      (ordNerveChain2 (ordStrictInclusion2 d)))) :
    ∃ d' : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d' =
        Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 d')) + Nerve.bdry y := by
  let b := cmap (oldCoveredSpineToOld q f) (ordNerveChain2 (ordStrictInclusion2 d))
  have hbi : b ∈ Inc P := cmap_mem_inc_of_monotone
    (oldCoveredSpineToOld_monotone q f) (ordNerveChain2_mem_inc _)
  have hbd : lengthProjection 3 b = b := by
    rw [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hzd : lengthProjection 3 (z - b) = z - b := by
    simp_all
  have hzc : Nerve.bdry (z - b) = 0 := by
    aesop
  obtain ⟨c, hc, y, hy, he⟩ := genus_old_cover_spine_cycle_generation q f hf
    _ ((Inc _).sub_mem hz hbi) hzd hzc
  refine ⟨d + c, ?_, y, hy, ?_⟩
  · aesop
  · simp only [map_add]
    have he' := congrArg (fun x : Ch P => x + b) he
    simp only [sub_add_cancel] at he'
    erw [he']
    abel

end FiniteChains.Davis.Genus
