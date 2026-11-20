module

public import RequestProject.CutPuncturedBoundaryAcyclic
public import RequestProject.GenusCutPairCollapse
public import RequestProject.PosetCoverPuncturedLower
public import RequestProject.NerveDegreeTransfer

@[expose] public section

/-! Fillings in the actual sheet of a top cube paired with its cut facet. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_cut_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List _)
    (t : QOld _) (hne : t.1.spx.Nonempty)
    (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    (v : P) (hv : f v = Sum.inl t) (n : ℕ) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v) n := by
  have g := recordedGeometry (s := Sum.inr (fullCutCell t hne)) hsplit
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inr _} ≃o
      CutPuncturedBoundary t hne := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by rfl }
  let E := (hf.puncturedLowerOrderIso v _).trans e
  have hfill := exists_bdry_eq_of_cycle_of_orderIso E
    (positiveCutPuncturedBoundary_acyclic t hne hpositive ht)
  have hnonempty : ∃ p : P, p < v ∧ f p ≠ Sum.inr (fullCutCell t hne) := by
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q _
      g.face_dim t ht
    exact ⟨(E.symm _).1, (E.symm ⟨x, hxt, hxs⟩).2⟩
  have he (p : P) : (p < v ∧ f p ≠ Sum.inr (fullCutCell t hne)) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨g.boundary _ ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · exact fun h => ⟨h.2, h.1.2⟩
  apply fillsDegreeIn_congr he
  apply fillsDegreeIn_of_subtype hnonempty
  solve_by_elim

end FiniteChains.Davis.Genus
