import RequestProject.PuncturedCubeCoverFillings
import RequestProject.PosetCoverPuncturedLower
import RequestProject.NerveMaximalDeletion
import RequestProject.OrderNervePositiveFillings
import RequestProject.GenusOrdinaryPairCollapse


/-! The actual ordinary genus-collapse top-cell step preserves H2 in every cover. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Both required lower-link fillings in the actual sheet of a lifted top cube.
Earlier collapse stages do not remove any other boundary cells. -/
theorem genus_ordinary_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    s t
    (hs : s.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right))
    v (hv : f v = Sum.inl t) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 2 ∧
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 3 := by
  let pair : GenusCollapsePair q :=
    (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by tauto
  have hcert := genusCollapseStage_suffix_certificate q left _ hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex _)
      (Sum.inl (qCubeToCoordinate s.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex _) (Sum.inl (qCubeToCoordinate s.1)) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex _)) left := by
      rw [hcert.2.1]
      exact Finset.mem_singleton_self _
    simp_all
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inl s} ≃o
      OldPuncturedBoundary s t := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by rfl }
  have hcover := (hf.puncturedLower_isPosetCover v _).postcompose_orderIso e
  have hfill := ordinaryTruncatedBoundary_cover_fillings hordinary hi hcover
  have hne : ∃ p : P, p < v ∧ f p ≠ Sum.inl s := by
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl s) hs t ht
    cases' hcover.surj ⟨x, hxt, hxs⟩ with p hp
    grind
  have he (p : P) : (p < v ∧ f p ≠ Sum.inl s) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨genusCollapseStage_boundary_mem q left (pair :: right) hsplit t htail
        (f p) ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    simp_all
  constructor
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_oneCycle_filling_of_strict hfill.1
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_twoCycle_filling_of_strict hfill.2
