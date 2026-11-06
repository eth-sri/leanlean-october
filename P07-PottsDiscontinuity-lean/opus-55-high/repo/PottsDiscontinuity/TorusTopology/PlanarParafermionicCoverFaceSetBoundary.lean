/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

@[instance_reducible] def coverFaceSetLocallyFinite
    {V : Type*} [Fintype V] (G : SimpleGraph V) : LocallyFinite G := fun v =>
  Fintype.ofInjective (fun x : G.neighborSet v => x.1) Subtype.val_injective

theorem faceSymmDiffList_even_degree {V I : Type*} [Fintype V]
    [DecidableEq V] (F : I → SimpleGraph V)
    (hF : ∀ i v, Even ((F i).neighborSet v).ncard) :
    ∀ L : List I, ∀ v, Even ((faceSymmDiffList F L).neighborSet v).ncard := by
  intro L
  induction L with
  | nil =>
    simp [faceSymmDiffList]
  | cons i L ih =>
    intro v
    let  := coverFaceSetLocallyFinite (F i)
    let  :=
      coverFaceSetLocallyFinite (faceSymmDiffList F L)
    let  :=
      coverFaceSetLocallyFinite (F i ∆ faceSymmDiffList F L)
    have hFi : ∀ v, Even ((F i).degree v) := by
      intro w
      simpa using hF i w
    have htail : ∀ v, Even ((faceSymmDiffList F L).degree v) := by
      simp_all
    have hdegree := degree_even_symmDiff (F i) (faceSymmDiffList F L) hFi htail v
    simp_all [Even, faceSymmDiffList]

def parafermionicCoverFiniteFaceSetBoundaryGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  faceSymmDiffList
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
theorem parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree  :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((parafermionicCoverFiniteFaceSetBoundaryGraph S).neighborSet v).ncard := by
  intro v
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  have hF : ∀ i v, Even ((F i).neighborSet v).ncard := by
    intro i v
    have he := parafermionicCoverFiniteFaceBoundaryGraph_even_degree i.1 i.2 v
    grind [parafermionicCoverFiniteFaceBoundaryDegree]
  simpa only [parafermionicCoverFiniteFaceSetBoundaryGraph, F] using (faceSymmDiffList_even_degree F hF S.toList v)

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff  :
    parafermionicCoverFiniteFaceSetBoundaryGraph S = ⊥ ↔ S = ∅ := by
  constructor
  · intro h
    have hEq : faceSymmDiffList
        (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
          parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList =
        faceSymmDiffList
          (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
            parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) [] := by
      tauto
    have hsets := parafermionicCoverFiniteFaceChain_toFinset_unique
      S.toList [] S.nodup_toList List.nodup_nil hEq
    simp_all
  · rintro rfl
    simp [parafermionicCoverFiniteFaceSetBoundaryGraph, faceSymmDiffList]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff  :
    parafermionicCoverFiniteFaceSetBoundaryGraph S ≠ ⊥ ↔ S.Nonempty := by
  grind [parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet :=
  parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
    S S.toList S.nodup_toList (by simp) u v
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
