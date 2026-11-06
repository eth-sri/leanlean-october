/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

abbrev CoverFiniteFaceDart (f : ParafermionicCoverVertex) :=
  {d : ParafermionicCoverVertex × ParafermionicCoverVertex //
    d ∈ parafermionicCoverFiniteFaceDarts f}

def coverFaceDartBoxPair {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) (d : CoverFiniteFaceDart f) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  (⟨d.1.1, (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf d.2).1⟩,
   ⟨d.1.2, (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf d.2).2⟩)

theorem coverFiniteFaceRawEdge_iff_dart (f : ParafermionicCoverVertex)
    (e : Sym2 ParafermionicCoverVertex) :
    e ∈ ({parafermionicCoverFiniteFaceBottomEdge f,
         parafermionicCoverFiniteFaceRightEdge f,
         parafermionicCoverFiniteFaceTopEdge f,
         parafermionicCoverFiniteFaceLeftEdge f} : Set (Sym2 ParafermionicCoverVertex)) ↔
      ∃ d : CoverFiniteFaceDart f, e = s(d.1.1, d.1.2) := by
  simp [CoverFiniteFaceDart, parafermionicCoverFiniteFaceDarts,
    parafermionicCoverFiniteFaceBottomEdge, parafermionicCoverFiniteFaceRightEdge,
    parafermionicCoverFiniteFaceTopEdge, parafermionicCoverFiniteFaceLeftEdge]

section
variable {n : ℕ} (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
theorem coverFaceDart_boxEdge_orientation (d : CoverFiniteFaceDart f) {u v : ParafermionicCoverBoxVertex n}
    (he : s(u,v) = s((coverFaceDartBoxPair f hf d).1,
      (coverFaceDartBoxPair f hf d).2)) :
    d.1 = (u.1, v.1) ∨ d.1 = (v.1, u.1) := by
  rcases Sym2.eq_iff.mp he.symm with h | h
  · exact Or.inl (Prod.ext (congrArg Subtype.val h.1) (congrArg Subtype.val h.2))
  · exact Or.inr (Prod.ext (congrArg Subtype.val h.1) (congrArg Subtype.val h.2))

theorem coverFiniteFaceBoundaryEdge_iff_dartSubtype (e : Sym2 (ParafermionicCoverBoxVertex n)) :
    e ∈ (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet ↔
      ∃ d : CoverFiniteFaceDart f,
        e = s((coverFaceDartBoxPair f hf d).1, (coverFaceDartBoxPair f hf d).2) := by
  constructor
  · intro he
    have hmap := Set.mem_image_of_mem (Sym2.map Subtype.val) he
    rw [parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet] at hmap
    have hraw : Sym2.map Subtype.val e ∈
        ({parafermionicCoverFiniteFaceBottomEdge f,
         parafermionicCoverFiniteFaceRightEdge f,
         parafermionicCoverFiniteFaceTopEdge f,
         parafermionicCoverFiniteFaceLeftEdge f} : Set (Sym2 ParafermionicCoverVertex)) := by
      omega
    obtain ⟨d, hd⟩ := (coverFiniteFaceRawEdge_iff_dart f _).mp hraw
    refine ⟨d, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    tauto
  · rintro ⟨d, rfl⟩
    have hraw : Sym2.map Subtype.val
        (s((coverFaceDartBoxPair f hf d).1, (coverFaceDartBoxPair f hf d).2)) ∈
        ({parafermionicCoverFiniteFaceBottomEdge f,
         parafermionicCoverFiniteFaceRightEdge f,
         parafermionicCoverFiniteFaceTopEdge f,
         parafermionicCoverFiniteFaceLeftEdge f} : Set (Sym2 ParafermionicCoverVertex)) :=
      (coverFiniteFaceRawEdge_iff_dart f _).mpr ⟨d, rfl⟩
    rw [← parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet] at hraw
    obtain ⟨e', he', hmap⟩ := (Set.mem_image _ _ _).mp hraw
    have heq :=
      Sym2.map.injective Subtype.val_injective hmap
    simpa [heq] using he'

theorem parafermionicCoverFiniteFaceBoundaryEdge_iff_darts (u v : ParafermionicCoverBoxVertex n) :
    s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet ↔
      (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts f ∨
      (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts f := by
  rw [coverFiniteFaceBoundaryEdge_iff_dartSubtype]
  constructor
  · rintro ⟨d, he⟩
    rcases coverFaceDart_boxEdge_orientation f hf d he with horient | horient <;> aesop
  · rintro (h | h)
    · let d : CoverFiniteFaceDart f := ⟨(u.1,v.1),h⟩
      tauto
    · let d : CoverFiniteFaceDart f := ⟨(v.1,u.1),h⟩
      exact ⟨d, by aesop⟩
end

theorem parafermionicCoverFiniteFaceBoundaryDistinctFaces_oppositeDarts {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (e : Sym2 (ParafermionicCoverBoxVertex n))
    (hi : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    ∃ a b : ParafermionicCoverVertex,
      (a,b) ∈ parafermionicCoverFiniteFaceDarts i.1 ∧
      (b,a) ∈ parafermionicCoverFiniteFaceDarts j.1 ∧
      Sym2.map Subtype.val e = s(a,b) := by
  obtain ⟨di, hdi⟩ := (coverFiniteFaceBoundaryEdge_iff_dartSubtype i.1 i.2 e).mp hi
  obtain ⟨dj, hdj⟩ := (coverFiniteFaceBoundaryEdge_iff_dartSubtype j.1 j.2 e).mp hj
  rcases (coverFaceDart_boxEdge_orientation j.1 j.2 dj (hdi.symm.trans hdj)) with hsame | hopposite
  · have hsame' : dj.1 = di.1 := by
      tauto
    have hdj' : di.1 ∈ parafermionicCoverFiniteFaceDarts j.1 := by
      rw [← hsame']
      simp
    have hfaces :=
      parafermionicCoverFiniteFaceDart_unique n i.2 j.2 di.2 hdj'
    simp_all
  · have hopposite' : dj.1 = (di.1.2, di.1.1) := by
      tauto
    let a := di.1.1
    let b := di.1.2
    have hopposite'' : dj.1 = (b,a) := by omega
    refine ⟨a,b,by simp [a,b],?_,?_⟩
    rw [← hopposite'']
    exact dj.2
    aesop

section
variable {n : ℕ} (e : Sym2 (ParafermionicCoverBoxVertex n))
noncomputable def parafermionicCoverFiniteFaceIncidentFaces  :
    Finset (ParafermionicCoverFiniteFaceTopIndex n) := by
  classical
  exact Finset.univ.filter fun i =>
    e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet

theorem parafermionicCoverFiniteFaceIncidentFaces_card_le_two  :
    (parafermionicCoverFiniteFaceIncidentFaces e).card ≤ 2 := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
    let S := parafermionicCoverFiniteFaceIncidentFaces (s(u,v))
    let d (i : S) :=
      Classical.choose ((coverFiniteFaceBoundaryEdge_iff_dartSubtype
        i.1.1 i.1.2 (s(u,v))).mp (Finset.mem_filter.mp i.2).2)
    have hd (i : S) :
        (d i).1 ∈ parafermionicCoverFiniteFaceDarts i.1.1 := by simp
    have he (i : S) :=
      Classical.choose_spec ((coverFiniteFaceBoundaryEdge_iff_dartSubtype
        i.1.1 i.1.2 (s(u,v))).mp (Finset.mem_filter.mp i.2).2)
    have hclass (i : S) :=
      coverFaceDart_boxEdge_orientation i.1.1 i.1.2 (d i) (he i)
    let orient (i : S) := if (d i).1 = (u.1,v.1) then true else false
    have hforward (i : S) (ho : orient i = true) : (d i).1 = (u.1,v.1) := by
      by_contra h
      have : orient i = false := by simp [orient, h]
      rw [ho] at this
      tauto
    have hbackward (i : S) (ho : orient i = false) : (d i).1 = (v.1,u.1) := by
      rcases hclass i with hfwd | hrev
      · have : orient i = true := by simp [orient, hfwd]
        rw [ho] at this
        tauto
      omega
    have hinj : Function.Injective orient := by
      intro i j hij
      cases oi : orient i <;> cases oj : orient j
      · have hfaces := parafermionicCoverFiniteFaceDart_unique n i.1.2 j.1.2 (hd i) (by
          rw [((hbackward i oi).trans (hbackward j oj).symm)]
          simp)
        exact Subtype.ext (Subtype.ext hfaces)
      · rw [oi, oj] at hij
        tauto
      · rw [oi, oj] at hij
        tauto
      · have hfaces := parafermionicCoverFiniteFaceDart_unique n i.1.2 j.1.2 (hd i) (by
          rw [((hforward i oi).trans (hforward j oj).symm)]
          simp)
        exact Subtype.ext (Subtype.ext hfaces)
    simpa using (Fintype.card_le_of_injective orient hinj)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
