module

public import RequestProject.GenusOrdinaryPairCoverHomology
public import RequestProject.GenusCutPairCoverHomology
public import RequestProject.GenusCollapseIteration

@[expose] public section

/-! The entire chosen geometric collapse preserves H2 in arbitrary covers. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

variable (hf : IsPosetCover f)
include hf

theorem genus_pair_cover_homology
    (left right : List _) (pair : GenusCollapsePair q)
    (hsplit : genusChainCollapse q = left ++ pair :: right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 := by
  have hp : pair ∈ genusChainCollapse q := by
    rw [hsplit]
    simp
  obtain ⟨t, s, ht, hs⟩ := genus_pair_cells q pair hp
  have he : pair = (qCubeToCoordinate t.1, truncatedFaceIndex s) :=
    Prod.ext ht.symm hs.symm
  rw [he] at hsplit ⊢
  cases s with
  | inl s => apply genus_ordinary_pair_cover_homology <;> assumption
  | inr σ => apply genus_recorded_cut_pair_cover_homology <;> assumption

/-- All intermediate comparisons use chains on the actual surviving cells. -/
theorem genus_collapse_suffix_cover_homology
    (right left : List _)
    (hsplit : genusChainCollapse q = left ++ right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 := by
  induction right generalizing left with
  | nil =>
    simp only [List.append_nil]
    constructor
    · intro z hz _ hcyc
      exact ⟨z, hz, 0, AddSubgroup.zero_mem _, hcyc, by simp⟩
    · solve_by_elim
  | cons pair right ih =>
    have hfirst := genus_pair_cover_homology q hf left right pair hsplit
    have htail := ih (left ++ [pair]) (by grind)
    have hgen := generatesDegreeIn_trans
      (fun p hp => genusCollapseStage_append_subset q left [pair] (f p) hp)
      hfirst.1 htail.1
    have href := reflectsBoundsIn_trans
      (fun p hp => genusCollapseStage_append_subset q (left ++ [pair]) right (f p) hp)
      hfirst.2 htail.2
    simpa only [List.append_assoc, List.singleton_append] using And.intro hgen href

/-- The actual surviving spine and the whole truncated block have the same H2
in every poset cover, including infinitely many sheets. This asserts both chain
generation and reflection of boundaries, with no homology premise. -/
theorem genusSpine_cover_homology :
    GeneratesDegreeIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 ∧
    ReflectsBoundsIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 := by
  have h := genus_collapse_suffix_cover_homology q hf (genusChainCollapse q) [] (by simp)
  simp_all [genusCollapseStage_nil, genusCollapseStage_final_iff]

end FiniteChains.Davis.Genus
