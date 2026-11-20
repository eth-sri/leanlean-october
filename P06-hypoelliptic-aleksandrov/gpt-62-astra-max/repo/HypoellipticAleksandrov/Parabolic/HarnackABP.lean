module

public import HypoellipticAleksandrov.Parabolic.ABP
public import HypoellipticAleksandrov.Parabolic.ExponentialConjugation
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# The local ABP bridge for the parabolic Harnack argument

This file proves the translated, radius-one-half ABP consequence used in
Krylov--Safonov Lemma 3.2.  It turns local classical data on the inner
cylinder into the globally regular data required by the unit ABP
estimate, removes the zeroth-order term by exponential conjugation, and then
uses the exact parabolic restricted-norm scaling formula.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped MatrixOrder Topology

section
variable {d : ℕ} (v0 : PDE.Vec d)

include v0 in
/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)

include v0 in
/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0

include v0 in
/-- The compact closure of the local inner ABP cylinder. -/
def localABPClosure : Set (TimeVelocity d) :=
  localABPAffine v0 '' closedParabolicCylinder 1 0

include v0 in
/-- The initial-plus-lateral, but not terminal, boundary of the local ABP
cylinder. -/
def localABPForwardBoundary : Set (TimeVelocity d) :=
  localABPAffine v0 '' forwardParabolicBoundary 1 0

/-- The local ABP closure is compact. -/
theorem isCompact_localABPClosure :
    IsCompact (localABPClosure v0) := by
  exact (isCompact_closedParabolicCylinder 1 0).image
    (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous

/-- The local ABP interior is contained in its compact closure. -/
theorem localABPInterior_subset_closure :
    localABPInterior v0 ⊆ localABPClosure v0 := by
  exact Set.image_mono (parabolicInterior_subset_closedParabolicCylinder 1 0)

private theorem forwardParabolicBoundary_subset_closedParabolicCylinder_one :
    forwardParabolicBoundary 1 (0 : PDE.Vec d) ⊆
      closedParabolicCylinder 1 0 := by
  intro z hz
  rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
  · aesop
  · rcases z with ⟨t, v⟩
    rcases hlateral with ⟨ht0, ht1, hsphere⟩
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨ht0, ht1, by
        exact hsphere.le⟩

/-- The local forward boundary is contained in the compact local ABP closure. -/
theorem localABPForwardBoundary_subset_closure :
    localABPForwardBoundary v0 ⊆ localABPClosure v0 := by
  exact Set.image_mono forwardParabolicBoundary_subset_closedParabolicCylinder_one

/-- The terminal centre is in the local ABP closure. -/
theorem localABPTarget_mem_closure :
    (1, v0) ∈ localABPClosure v0 := by
  refine ⟨(1, 0), ?_, ?_⟩
  · exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
      change PDE.euclideanSqDist 0 0 ≤ 1 ^ 2
      simp⟩
  simp_all [localABPAffine, parabolicAffine] <;> linarith

private theorem localABPAffine_referenceTarget :
    localABPAffine v0 (1, 0) = (1, v0) := by
  simp_all [localABPAffine, parabolicAffine] <;> linarith

private theorem referenceTarget_mem_closedParabolicCylinder :
    (1, 0) ∈ closedParabolicCylinder 1 (0 : PDE.Vec d) := by
  exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
    change PDE.euclideanSqDist 0 0 ≤ 1 ^ 2
    simp⟩

end

private theorem eventualEq_nhds_of_eventualEq_nhdsSet {α : Type*}
    {β : Type*} [TopologicalSpace α] {K : Set α} {f g : α → β} {x : α}
    (hx : x ∈ K) (hfg : f =ᶠ[𝓝ˢ K] g) : f =ᶠ[𝓝 x] g :=
  (eventually_nhdsSet_iff_forall.mp hfg x hx)

variable (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam)
include hd hlam

/-- Common proof of the local ABP consequences with ellipticity on the compact
cylinder actually used by the cutoff-and-pullback construction. -/
private theorem exists_local_abp_inner_cylinder_core :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
  obtain ⟨C, hC, hABP⟩ :=
    parabolic_abp_unit_of_lower_ellipticity d hd lam hlam
  refine ⟨C, hC, ?_⟩
  intro U B w F v0 rho hU hKU hB hw hF hLow hFnonneg hineq hboundary
  let K := localABPClosure v0
  obtain ⟨b, hbSmooth, hbOne, hbSupport⟩ :=
    exists_smooth_cutoff_tsupport_subset (isCompact_localABPClosure v0) hU hKU
  let ew := exponentialConjugate rho (3 / 4) w
  let H := fun z => exponentialTimeWeight rho (3 / 4) z * F z
  let g := fun z => b z * ew z
  let G := fun z => b z * H z
  let Bbar := cutoffExtendCoefficient b B lam
  have hH : ContinuousOn H U := by
    exact (contDiff_exponentialTimeWeight rho (3 / 4)).continuous.continuousOn.mul hF
  have hEW : ContDiffOn ℝ 2 ew U := by
    exact contDiffOn_exponentialConjugate hw
  have hconj : IsParabolicSubsolutionOn B H ew (localABPInterior v0) := by
    intro z hz
    have hzU := hKU (localABPInterior_subset_closure v0 hz)
    dsimp only [H, ew]
    rw [parabolicOperator_exponentialConjugate B
      (hw.contDiffAt (hU.mem_nhds hzU))]
    exact mul_le_mul_of_nonneg_left (hineq z hz)
      (exponentialTimeWeight_pos rho (3 / 4) z).le
  have hg : ContDiff ℝ 2 g := by
    dsimp only [g]
    exact contDiff_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hEW
  have hG : Continuous G := by
    dsimp only [G]
    exact continuous_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hH
  have hBbar : IsContinuousCoefficient Bbar := by
    dsimp only [Bbar]
    exact continuous_coefficientAt_cutoffExtendCoefficient hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hB
  have hgEq : g =ᶠ[𝓝ˢ K] ew := by
    exact cutoff_mul_eventuallyEq hbOne
  have hGEq : G =ᶠ[𝓝ˢ K] H := by
    exact cutoff_mul_eventuallyEq hbOne
  have hBbarEq : coefficientAt Bbar =ᶠ[𝓝ˢ K] coefficientAt B := by
    exact coefficientAt_cutoffExtendCoefficient_eventuallyEq hbOne
  have hlocalSub : IsParabolicSubsolutionOn Bbar G g (localABPInterior v0) := by
    intro x hx
    have hxK := localABPInterior_subset_closure v0 hx
    have hgx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hgEq
    have hBx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hBbarEq
    calc
      parabolicOperator Bbar g x = parabolicOperator B ew x := (parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq hBx hgx)
      _ ≤ H x := hconj x hx
      _ = G x := ((eventualEq_nhds_of_eventualEq_nhdsSet hxK hGEq).self_of_nhds).symm
  let a := localABPAffine v0
  let Bhat := pullbackCoefficient Bbar (3 / 4) v0 (1 / 2)
  let uhat := pullbackScalar g (3 / 4) v0 (1 / 2)
  let fhat := fun z => (1 / 2) ^ 2 * G (a z)
  have haCont : Continuous a := by
    exact (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous
  have hBhat : IsContinuousCoefficient Bhat := by
    exact hBbar.comp haCont
  have huhat : ContDiff ℝ 2 uhat := by
    exact hg.comp (contDiff_parabolicAffine (3 / 4) v0 (1 / 2))
  have hfhat : Continuous fhat := by
    fun_prop
  have hLowHat : ∀ z ∈ closedParabolicCylinder 1 0,
      lam • 1 ≤ coefficientAt Bhat z := by
    intro z hz
    have hzK : a z ∈ K := ⟨z, hz, rfl⟩
    have hBz := eventualEq_nhds_of_eventualEq_nhdsSet hzK hBbarEq
    change lam • 1 ≤ coefficientAt Bbar (a z)
    rw [hBz.self_of_nhds]
    exact hLow (a z) hzK
  have hsubHat : IsParabolicSubsolutionOn Bhat fhat uhat
      (parabolicInterior 1 0) := by
    intro z hz
    rw [show parabolicOperator Bhat uhat z =
        (1 / 2) ^ 2 * parabolicOperator Bbar g (a z) by
      exact parabolicOperator_pullbackScalar hg.contDiffAt]
    exact mul_le_mul_of_nonneg_left (hlocalSub (a z) ⟨z, hz, rfl⟩) (sq_nonneg (1 / 2))
  have hboundaryHat : ∀ z ∈ forwardParabolicBoundary 1 0,
      uhat z ≤ 0 := by
    intro z hz
    have hza : a z ∈ localABPForwardBoundary v0 := ⟨z, hz, rfl⟩
    have hgz := eventualEq_nhds_of_eventualEq_nhdsSet (localABPForwardBoundary_subset_closure v0 hza) hgEq
    have hew : ew (a z) ≤ 0 := by
      exact (exponentialConjugate_nonpos_iff rho (3 / 4) w (a z)).mpr
        (hboundary (a z) hza)
    change uhat z ≤ 0
    change g (a z) ≤ 0
    rw [hgz.self_of_nhds]
    exact hew
  have hABPPoint := hABP (T := 1) (by norm_num) (by norm_num)
    0 Bhat fhat uhat hBhat hfhat huhat hLowHat hsubHat hboundaryHat
      (1, 0) referenceTarget_mem_closedParabolicCylinder
  have hmaxAE :
      (fun z => max (fhat z) 0) =ᵐ[volume.restrict (parabolicInterior 1 0)]
        fun z => (1 / 2) ^ 2 * H (a z) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior 1 0)]
      with z hz
    have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
    have hGz := eventualEq_nhds_of_eventualEq_nhdsSet (localABPInterior_subset_closure v0 hza) hGEq
    have hHnonneg : 0 ≤ H (a z) := by
      exact mul_nonneg (exponentialTimeWeight_pos rho (3 / 4) (a z)).le
        (hFnonneg (a z) hza)
    dsimp only [fhat]
    rw [hGz.self_of_nhds, max_eq_left]
    positivity
  have hnormMax :
      parabolicLpNormOn d (fun z => max (fhat z) 0)
          (parabolicInterior 1 0) =
        parabolicLpNormOn d (fun z => (1 / 2) ^ 2 * H (a z))
          (parabolicInterior 1 0) := by
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hmaxAE)
  have hnorm := parabolicLpNormOn_pullback (d := d) (3 / 4) v0
    (by norm_num : 0 < (1 / 2 : ℝ)) H (parabolicInterior 1 0)
  have hnorm' :
      parabolicLpNormOn d (fun z => (1 / 2) ^ 2 * H (a z))
          (parabolicInterior 1 0) =
        (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    simpa only [a, H, localABPAffine, localABPInterior] using hnorm
  have htargetK : (1, v0) ∈ K := by
    apply localABPTarget_mem_closure
  have htargetWeight : exponentialTimeWeight rho (3 / 4) (1, v0) =
      Real.exp (rho / 4) := by
    rw [exponentialTimeWeight_apply]
    ring
  have hweighted :
      exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤
        C * (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    have huTarget : uhat (1, 0) = g (1, v0) := by
      exact congrArg g (by
        simpa only [localABPAffine] using localABPAffine_referenceTarget v0)
    rw [huTarget, (eventualEq_nhds_of_eventualEq_nhdsSet htargetK hgEq).self_of_nhds] at hABPPoint
    change exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤ _
      at hABPPoint
    rw [hnormMax, hnorm'] at hABPPoint
    simpa only [mul_assoc] using hABPPoint
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    w (1, v0) = Real.exp (-rho / 4) *
        (exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0)) := by
      grind
    _ ≤ Real.exp (-rho / 4) *
        (C * (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0)) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
    _ = C * (1 / 2) ^ ((d : ℝ) / (d + 1)) *
          Real.exp (-rho / 4) *
            parabolicLpNormOn d
              (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
              (localABPInterior v0) := by
      dsimp only [H, exponentialTimeWeight]
      ring

/-- The local ABP consequence requiring lower ellipticity only on the compact
local cylinder used by its cutoff-and-pullback proof. -/
theorem exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
  exact exists_local_abp_inner_cylinder_core d hd lam hlam

end HypoellipticAleksandrov.Parabolic
