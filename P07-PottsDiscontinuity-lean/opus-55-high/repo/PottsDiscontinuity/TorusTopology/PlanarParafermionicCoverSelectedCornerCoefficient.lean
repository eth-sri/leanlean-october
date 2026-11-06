/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceCornerCompass
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCorners

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (v w : ParafermionicCoverBoxVertex n) (d : Fin 4) (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d)
include hd
theorem selectedCornerCoeff_forward_count_one_iff  :
    parafermionicCoverFacePositiveDartCount S v w = 1 ↔
      d ∈ parafermionicCoverFiniteFaceSelectedCorners S v := by
  constructor
  · intro hcount
    have hcard : (S.filter fun i => (v.1,w.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card = 1 := by
      tauto
    have hpos : 0 < (S.filter fun i => (v.1,w.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rcases Finset.mem_filter.mp hi with ⟨hiS, hdart⟩
    obtain ⟨c, hvc, hwc⟩ :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i v.1 w.1).mp hdart
    have hdir : c = d := by
      apply parafermionicCoverCompassNeighbor_injective v.1
      simp_all
    subst c
    exact (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v d).2
      ⟨i, hiS, hvc.symm⟩
  · intro hcorner
    rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v d).mp hcorner with
      ⟨i, hiS, hvc⟩
    have hdart :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i v.1 w.1).2
        ⟨d, hvc.symm, hd⟩
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S v w :=
      Finset.card_pos.mpr ⟨i, (by simp_all)⟩
    have hle := coverFaceSetPositiveDartCount_le_one S v w
    omega

theorem selectedCornerCoeff_reverse_count_one_iff  :
    parafermionicCoverFacePositiveDartCount S w v = 1 ↔
      d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v := by
  constructor
  · intro hcount
    have hcard : (S.filter fun i => (w.1,v.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card = 1 := by
      tauto
    have hpos : 0 < (S.filter fun i => (w.1,v.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rcases Finset.mem_filter.mp hi with ⟨hiS, hdart⟩
    obtain ⟨c, hwc, hvc⟩ :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i w.1 v.1).mp hdart
    have hc : d + 2 = c := by
      apply parafermionicCoverCompassNeighbor_injective w.1
      calc
        parafermionicCoverCompassNeighbor w.1 (d + 2) = v.1 := by
          rw [hd]
          exact parafermionicCoverCompassNeighbor_reverse v.1 d
        _ = parafermionicCoverCompassNeighbor w.1 c := hvc
    have hcorner : parafermionicCoverFaceCorner i.1 (d - 1) = v.1 := by
      have hnext := parafermionicCoverFiniteFaceCorner_next_compass i c
      grind
    exact (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v (d - 1)).2
      ⟨i, hiS, hcorner⟩
  · intro hcorner
    rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v (d - 1)).mp hcorner with
      ⟨i, hiS, hvc⟩
    have hprev := parafermionicCoverFiniteFaceCorner_prev_compass i (d - 1)
    have hcorneridx : (d - 1) - 1 = d + 2 := by omega
    have hfirst : parafermionicCoverFaceCorner i.1 (d + 2) = w.1 := by
      simp_all
    have hback : parafermionicCoverCompassNeighbor w.1 (d + 2) = v.1 := by
      rw [hd]
      exact parafermionicCoverCompassNeighbor_reverse v.1 d
    have hdart :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i w.1 v.1).2
        ⟨d + 2, hfirst.symm, hback.symm⟩
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S w v :=
      Finset.card_pos.mpr ⟨i, (by simp_all)⟩
    have hle := coverFaceSetPositiveDartCount_le_one S w v
    omega

/-- A directed positive-dart count along compass direction `d` is the
indicator that `d` is a selected corner at its source. -/
theorem parafermionicCoverFacePositiveDartCount_eq_selectedCornerIndicator
     :
    parafermionicCoverFacePositiveDartCount S v w =
      if d ∈ parafermionicCoverFiniteFaceSelectedCorners S v then 1 else 0 := by
  grind [parafermionicCoverFiniteFaceSelectedCorners, selectedCornerCoeff_forward_count_one_iff, parafermionicCoverFacePositiveDartCount, coverFaceSetPositiveDartCount_le_one]

/-- The reversed edge count is the indicator at the preceding corner. -/
theorem parafermionicCoverFacePositiveDartCount_reverse_eq_selectedCornerIndicator
     :
    parafermionicCoverFacePositiveDartCount S w v =
      if d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v then 1 else 0 := by
  by_cases hcorner : d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v
  · have hone := (selectedCornerCoeff_reverse_count_one_iff S v w d hd).2 hcorner
    simp_all
  · have hne : parafermionicCoverFacePositiveDartCount S w v ≠ 1 := by
      intro hone
      exact hcorner ((selectedCornerCoeff_reverse_count_one_iff S v w d hd).1 hone)
    grind [coverFaceSetPositiveDartCount_le_one]

/-- The oriented coefficient is the integer difference of the two adjacent
corner indicators. -/
theorem parafermionicCoverFaceBoundaryCoefficient_eq_selectedCornerIndicators
     :
    parafermionicCoverFaceBoundaryCoefficient S v w =
      (if d ∈ parafermionicCoverFiniteFaceSelectedCorners S v then (1 : ℤ) else 0) -
      (if d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v then (1 : ℤ) else 0) := by
  rw [parafermionicCoverFaceBoundaryCoefficient,
    parafermionicCoverFacePositiveDartCount_eq_selectedCornerIndicator S v w d hd,
    parafermionicCoverFacePositiveDartCount_reverse_eq_selectedCornerIndicator S v w d hd]
  simp
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
