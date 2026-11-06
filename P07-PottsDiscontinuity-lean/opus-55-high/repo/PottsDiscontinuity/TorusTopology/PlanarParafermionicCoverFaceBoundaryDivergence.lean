/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (f : ParafermionicCoverVertex)
def coverFaceDartList  :
    List (ParafermionicCoverVertex × ParafermionicCoverVertex) :=
  [(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
     parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
     parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f)]


theorem coverFaceDartList_nodup  :
    (coverFaceDartList f).Nodup := by
  rcases f with ⟨⟨x,y⟩,k⟩
  simp [ParafermionicCoverVertex, coverFaceDartList]

theorem coverFaceDartList_toFinset  :
    (coverFaceDartList f).toFinset = parafermionicCoverFiniteFaceDarts f := by
  simp [coverFaceDartList, parafermionicCoverFiniteFaceDarts]
end

section
variable {n : ℕ} (D : Finset (ParafermionicCoverVertex × ParafermionicCoverVertex))
theorem sum_outgoing_dart_indicator (hend : ∀ d ∈ D, d.2 ∈ parafermionicCoverBoxVertices n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ D then (1 : ℤ) else 0) =
      ∑ d ∈ D, if d.1 = u.1 then (1 : ℤ) else 0 := by
  calc
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ D then (1 : ℤ) else 0) =
        ∑ v : ParafermionicCoverBoxVertex n,
          ∑ d ∈ D, if d = (u.1,v.1) then (1 : ℤ) else 0 := by
      simp
    _ = ∑ d ∈ D, ∑ v : ParafermionicCoverBoxVertex n,
        if d = (u.1,v.1) then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, if d.1 = u.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      let w : ParafermionicCoverBoxVertex n := ⟨d.2, hend d hd⟩
      by_cases hsource : d.1 = u.1
      · rw [Finset.sum_eq_single w]
        · grind
        · grind
        grind
      · rw [Finset.sum_eq_zero]
        · simp_all
        grind

theorem sum_incoming_dart_indicator (hstart : ∀ d ∈ D, d.1 ∈ parafermionicCoverBoxVertices n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ D then (1 : ℤ) else 0) =
      ∑ d ∈ D, if d.2 = u.1 then (1 : ℤ) else 0 := by
  calc
    (∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ D then (1 : ℤ) else 0) =
        ∑ v : ParafermionicCoverBoxVertex n,
          ∑ d ∈ D, if d = (v.1,u.1) then (1 : ℤ) else 0 := by
      simp
    _ = ∑ d ∈ D, ∑ v : ParafermionicCoverBoxVertex n,
        if d = (v.1,u.1) then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, if d.2 = u.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      let w : ParafermionicCoverBoxVertex n := ⟨d.1, hstart d hd⟩
      by_cases htarget : d.2 = u.1
      · rw [Finset.sum_eq_single w]
        · grind
        · grind
        grind
      · rw [Finset.sum_eq_zero]
        · simp_all
        grind
end

theorem coverFaceDartSourceSum_eq_targetSum (f : ParafermionicCoverVertex)
    (u : ParafermionicCoverVertex) :
    (∑ d ∈ parafermionicCoverFiniteFaceDarts f,
      if d.1 = u then (1 : ℤ) else 0) =
    ∑ d ∈ parafermionicCoverFiniteFaceDarts f,
      if d.2 = u then (1 : ℤ) else 0 := by
  rw [← coverFaceDartList_toFinset f, List.sum_toFinset _ (coverFaceDartList_nodup f), List.sum_toFinset _ (coverFaceDartList_nodup f)]
  simp only [coverFaceDartList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem coverFaceVertexDartDivergence {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0) =
    ∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
  rw [sum_outgoing_dart_indicator _ (fun d hd =>
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hd).2) u]
  rw [sum_incoming_dart_indicator _ (fun d hd =>
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hd).1) u]
  exact coverFaceDartSourceSum_eq_targetSum i.1 u.1

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
theorem coverFacePositiveCount_eq_sum (u v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFacePositiveDartCount S u v : ℤ) =
      ∑ i ∈ S, if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then 1 else 0 := by
  aesop

theorem parafermionicCoverFaceBoundaryCoefficient_divergence (u : ParafermionicCoverBoxVertex n) :
    ∑ v : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient S u v = 0 := by
  unfold parafermionicCoverFaceBoundaryCoefficient
  rw [Finset.sum_sub_distrib]
  have hpos :
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S u v : ℤ)) =
        ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
    calc
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S u v : ℤ)) =
          ∑ v : ParafermionicCoverBoxVertex n, ∑ i ∈ S,
            if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        grind [coverFacePositiveCount_eq_sum]
      _ = ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        rw [Finset.sum_comm]
  have hneg :
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S v u : ℤ)) =
        ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
    calc
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S v u : ℤ)) =
          ∑ v : ParafermionicCoverBoxVertex n, ∑ i ∈ S,
            if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        simp [coverFacePositiveCount_eq_sum]
      _ = ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        rw [Finset.sum_comm]
  rw [hpos, hneg, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact sub_eq_zero.mpr (coverFaceVertexDartDivergence i u)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
