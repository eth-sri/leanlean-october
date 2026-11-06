module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryBuffer
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Literal sampling cylinder and topology of the buffered reference box -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

variable (d m : ℕ)

/-- The source's reference sampling center before its small dilation. -/
def samplingCenter  : KineticPoint d := ⟨-((m : ℝ) + 2), 0, 0⟩

/-- The source's reference sampling cylinder before its small dilation. -/
def samplingCylinder  : Set (KineticPoint d) :=
  backwardCylinder (samplingCenter d m) 1

/-- The buffered reference region is open in physical coordinates. -/
theorem isOpen_referenceRegion  (L : ℝ) : IsOpen (referenceRegion d m L) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
        continuous_const).inter
        (isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
          continuous_const)))

/-- A finite rectangular envelope bounds the reference region. -/
theorem isBounded_referenceRegion  {L : ℝ} (hL : 0 ≤ L) :
    Bornology.IsBounded (referenceRegion d m L) := (Bornology.IsBounded.subset
  (IsCompact.isBounded
    ((Homeomorph.isCompact_preimage (KineticPoint.homeomorphProd d)).mpr
      (IsCompact.prod isCompact_Icc
        (IsCompact.prod (PDE.isCompact_euclideanClosedBall 0 hL) (PDE.isCompact_euclideanClosedBall 0 hL)))))
  fun ⦃P⦄ hP =>
  ⟨⟨LT.lt.le hP.left, LT.lt.le hP.right.left⟩,
    ⟨(PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
        (id
          (Eq.mpr (id (congrFun' (congrArg LE.le (congrArg PDE.vecEuclideanNorm (sub_zero P.position))) L))
            (LT.lt.le hP.right.right.left))),
      (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
        (id
          (Eq.mpr (id (congrFun' (congrArg LE.le (congrArg PDE.vecEuclideanNorm (sub_zero P.velocity))) L))
            (LT.lt.le hP.right.right.right)))⟩⟩)

/-- Sampling closure coordinates have the exact unit Euclidean bounds. -/
theorem sampling_closure_bounds  (P : KineticPoint d)
    (hP : P ∈ closure (samplingCylinder d m)) :
    -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
  have hb := Covering.closure_cylinder_bounds _ 1 hP
  simp only [samplingCenter, relativePosition, sub_zero, smul_zero, one_pow] at hb
  refine ⟨by linarith only [hb.1], hb.2.1, ?_, ?_⟩
  ·

    nlinarith only [(PDE.vecEuclideanNorm_nonneg P.position), (PDE.vecEuclideanNorm_sq P.position), hb.2.2.2]
  ·

    nlinarith only [(PDE.vecEuclideanNorm_nonneg P.velocity), (PDE.vecEuclideanNorm_sq P.velocity), hb.2.2.1]

/-- The added time buffer strictly encloses the entire sampling-cylinder closure. -/
theorem sampling_closure_subset_reference  {L : ℝ} (hL : 1 < L) :
    closure (samplingCylinder d m) ⊆ referenceRegion d m L := by
  intro P hP
  obtain ⟨htlo, htup, hx, hv⟩ := sampling_closure_bounds d m P hP
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  exact ⟨by linarith only [htlo], by linarith only [htup, hm],
    hx.trans_lt hL, hv.trans_lt hL⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
