module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryImages
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPaths
import Mathlib.Tactic

/-! # One buffered reference region and one scale for every growth-lemma consumer -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/- The reference bound strictly exceeds one. -/
theorem referenceBound_large (m : ℕ) : 1 < referenceBound m := by
  have hb : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold referenceBound
  linarith only [hb, hm]

/- The target unit cylinder lies in the same reference region as the sampling closure. -/
theorem unitCylinder_subset_reference (d m : ℕ) :
    backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ⊆
      referenceRegion d m (referenceBound m) := by
  intro P hP
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL := referenceBound_large m
  have hpv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1)).mp hP.2.2.1
  have hpx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 ^ 3)).mp hP.2.2.2
  simp only [relativePosition, sub_zero, smul_zero, one_pow] at hpx hpv
  have htlo : -1 < P.time := by simpa only [one_pow, zero_sub] using hP.1
  exact ⟨by linarith only [htlo, hm], hP.2.1, hpx.trans hL, hpv.trans hL⟩

/- One smaller reference scale preserves all positivity and admissibility data. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
