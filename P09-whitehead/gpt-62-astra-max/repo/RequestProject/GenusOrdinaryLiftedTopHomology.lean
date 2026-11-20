module

public import RequestProject.PuncturedCubeCoverFillings
public import RequestProject.PosetCoverPuncturedLower
public import RequestProject.NerveBoundaryReflection
public import RequestProject.OrderNervePositiveFillings
public import RequestProject.GenusOrdinaryPairCollapse

@[expose] public section

/-! The actual ordinary genus-collapse top-cell step preserves H2 in every cover. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Both required lower-link fillings in the actual sheet of a lifted top cube.
Earlier collapse stages do not remove any other boundary cells. -/
theorem genus_ordinary_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hs : s.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right))
    (v : P) (hv : f v = Sum.inl t) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 2 ∧
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 3 := by
  have g := recordedGeometry (s := Sum.inl s) (t := t) hsplit
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inl s} ≃o
      OldPuncturedBoundary s t := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by rfl }
  have hcover := (hf.puncturedLower_isPosetCover v (Sum.inl s)).postcompose_orderIso e
  have hfill := ordinaryTruncatedBoundary_cover_fillings hordinary g.incident hcover
  have hne : ∃ p : P, p < v ∧ f p ≠ Sum.inl s := by
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl s) hs t ht
    obtain ⟨p, hp⟩ := hcover.surj ⟨x, hxt, hxs⟩
    exact ⟨p.1, p.2⟩
  have he (p : P) : (p < v ∧ f p ≠ Sum.inl s) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨g.boundary _ ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · exact fun h => ⟨h.2, h.1.2⟩
  constructor
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_oneCycle_filling_of_strict hfill.1
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_twoCycle_filling_of_strict hfill.2

end FiniteChains.Davis.Genus
