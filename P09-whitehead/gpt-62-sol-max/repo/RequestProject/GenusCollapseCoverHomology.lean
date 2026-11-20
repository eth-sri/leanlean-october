module

public import RequestProject.GenusCutPairCollapse
public import RequestProject.CutPuncturedBoundaryAcyclic
public import RequestProject.PuncturedCubeCoverFillings
public import RequestProject.PosetCoverFreeFaceHomology
public import RequestProject.PosetCoverPuncturedLower
public import RequestProject.NerveMaximalFamilyDeletion
public import RequestProject.NerveGenerationComposition
public import RequestProject.GenusCollapseIteration

@[expose] public section

/-! The entire chosen geometric collapse preserves H2 in arbitrary covers. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- The punctured boundary of either kind of recorded pair has an acyclic nerve. -/
theorem genus_punctured_boundary_acyclic {left right : List (GenusCollapsePair q)}
    {s : GenusTruncatedCell q} {t : QOld (cmpRel (GenusVertex q))}
    (h : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right) :
    ∀ c ∈ Inc {x : GenusTruncatedCell q // x < Sum.inl t ∧ x ≠ s}, Nerve.bdry c = 0 →
      ∃ y ∈ Inc {x : GenusTruncatedCell q // x < Sum.inl t ∧ x ≠ s}, Nerve.bdry y = c := by
  cases s with
  | inl s =>
    exact ordinaryTruncatedBoundary_acyclic (genus_old_pair_data q left right s t h).2.2
      (genus_pair_data q (s := Sum.inl s) h).incident
  | inr σ =>
    obtain ⟨hs, hne, ht, hp⟩ := genus_cut_pair_data q left right σ t h
    have he : σ = fullCutCell t hne := Subtype.ext hs.symm
    rw [he]
    exact positiveCutPuncturedBoundary_acyclic t hne hp ht

theorem genus_covered_link_fills (hf : IsPosetCover f)
    {left right : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
    {t : QOld (cmpRel (GenusVertex q))}
    (h : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right)
    (v : P) (hv : f v = Sum.inl t) (n : ℕ) :
    FillsDegreeIn (fun p => (genusCollapseStage q left (f p) ∧ f p ≠ s) ∧ p < v) n := by
  have d := genus_pair_data q h
  let E  :=
    (hf.puncturedLowerOrderIso v s).trans (by rw [hv])
  apply fillsDegreeIn_congr (A := fun p => p < v ∧ f p ≠ s) ?_
  · exact fillsDegreeIn_of_subtype
      (fun c hc _ hcyc => exists_bdry_eq_of_cycle_of_orderIso E
        (genus_punctured_boundary_acyclic q h) c hc hcyc)
  · intro p
    refine ⟨fun hp => ⟨⟨d.boundary_mem _ ?_, hp.2⟩, hp.1⟩, fun hp => ⟨hp.2, hp.1.2⟩⟩
    exact hv ▸ hf.strictMono hp.1

/-- Removing the lifted free faces and then the lifted maximal cubes compares the two stages. -/
theorem genus_recorded_pair_cover_homology (hf : IsPosetCover f)
    {left right : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
    {t : QOld (cmpRel (GenusVertex q))}
    (h : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)]) (f p)) 3 := by
  have d := genus_pair_data q h
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ s
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := fun p hp => ⟨hp ▸ d.top_mem, hp.trans_ne d.face_lt.ne.symm⟩
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    have hx := genus_top_cell_maximal q t d.dim_top (f x) (hp ▸ hf.mono hpx)
    exact hf.up_inj hpx le_rfl (hx.trans hp.symm)
  have htop := maximalFamily_homology hTC hmax
    (fun v hv => genus_covered_link_fills q hf h v hv 2)
    (fun v hv => genus_covered_link_fills q hf h v hv 3)
  have hface := cover_freeFace_homology hf d.top_mem d.face_lt.le d.face_lt.ne.symm d.unique_coface
  rw [funext fun p => propext (genusCollapseStage_step_iff q left s t (f p))]
  exact ⟨generatesDegreeIn_trans (fun _ hp => hp.1)
      (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ hp => hp.1) (hface.2 3) htop.2⟩

/-- The actual surviving spine and the whole truncated block have the same H2
in every poset cover, including infinitely many sheets. This asserts both chain
generation and reflection of boundaries, with no homology premise. -/
theorem genusSpine_cover_homology (hf : IsPosetCover f) :
    GeneratesDegreeIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 ∧
    ReflectsBoundsIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 := by
  let stage (l : List (GenusCollapsePair q)) := fun p => genusCollapseStage q l (f p)
  have h := genus_collapse_suffix q
    (R := fun l r => GeneratesDegreeIn (stage l) (stage r) 3 ∧ ReflectsBoundsIn (stage l) (stage r) 3)
    ?_ (genus_recorded_pair_cover_homology q hf) ?_ (l := []) (r := genusChainCollapse q) rfl
  · simpa only [stage, List.nil_append, genusCollapseStage_nil_eq, genusCollapseStage_full_eq] using h
  · refine fun _ => ⟨fun z hz _ hcyc => ⟨z, hz, 0, AddSubgroup.zero_mem _, hcyc, by simp⟩, ?_⟩
    tauto
  · intro l p r h₁ h₂
    exact ⟨generatesDegreeIn_trans
      (fun v => genusCollapseStage_append_subset q l [p] (f v)) h₁.1 h₂.1,
      reflectsBoundsIn_trans
        (fun v => genusCollapseStage_append_subset q (l ++ [p]) r (f v)) h₁.2 h₂.2⟩

end FiniteChains.Davis.Genus
