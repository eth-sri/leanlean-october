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

/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine {d : ℕ} (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)

/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0

/-- The compact closure of the local inner ABP cylinder. -/
def localABPClosure {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' closedParabolicCylinder 1 0

/-- The initial-plus-lateral, but not terminal, boundary of the local ABP
cylinder. -/
def localABPForwardBoundary {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' forwardParabolicBoundary 1 0

variable {d : ℕ} (v0 : PDE.Vec d)

/-- The local ABP closure is compact. -/
theorem isCompact_localABPClosure  :
    IsCompact (localABPClosure v0) := (isCompact_closedParabolicCylinder 1 0).image
    (contDiff_parabolicAffine _ v0 _).continuous

/-- The local ABP interior is contained in its compact closure. -/
theorem localABPInterior_subset_closure  :
    localABPInterior v0 ⊆ localABPClosure v0 := Set.image_mono (parabolicInterior_subset_closedParabolicCylinder 1 0)

private theorem forwardParabolicBoundary_subset_closedParabolicCylinder_one
     :
    forwardParabolicBoundary 1 (0 : PDE.Vec d) ⊆
      closedParabolicCylinder 1 0 := by
  intro z hz
  rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
  · rcases z with ⟨t, v⟩
    rcases hinitial with ⟨ht, hv⟩
    change t = 0 at ht
    subst t
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨by norm_num, by norm_num, hv⟩
  · rcases z with ⟨t, v⟩
    rcases hlateral with ⟨ht0, ht1, hsphere⟩
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨ht0, ht1, by
        exact hsphere.le⟩

/-- The local forward boundary is contained in the compact local ABP closure. -/
theorem localABPForwardBoundary_subset_closure  :
    localABPForwardBoundary v0 ⊆ localABPClosure v0 := Set.image_mono forwardParabolicBoundary_subset_closedParabolicCylinder_one

/-- The terminal centre is in the local ABP closure. -/
theorem localABPTarget_mem_closure  :
    (1, v0) ∈ localABPClosure v0 := by
  refine ⟨(1, 0), ?_, ?_⟩
  · exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
      change PDE.euclideanSqDist _ 0 ≤ 1 ^ 2
      simp⟩
  · simp only [localABPAffine, parabolicAffine]
    ext
    · norm_num [div_pow]
    · simp

private theorem localABPAffine_referenceTarget  :
    localABPAffine v0 (1, 0) = (1, v0) := by
  simp only [localABPAffine, parabolicAffine]
  ext
  · norm_num [div_pow]
  · simp

private theorem referenceTarget_mem_closedParabolicCylinder  :
    (1, 0) ∈ closedParabolicCylinder 1 (0 : PDE.Vec d) := mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
    change PDE.euclideanSqDist _ 0 ≤ 1 ^ 2
    simp⟩

private theorem eventualEq_nhds_of_eventualEq_nhdsSet {α : Type*}
    {β : Type*} [TopologicalSpace α] {K : Set α} {f g : α → β} {x : α}
    (hx : x ∈ K) (hfg : f =ᶠ[𝓝ˢ K] g) : f =ᶠ[𝓝 x] g :=
  (eventually_nhdsSet_iff_forall.mp hfg x hx)

/-- Common proof of the local ABP consequences with ellipticity on the compact
cylinder actually used by the cutoff-and-pullback construction. -/
private theorem exists_local_abp_inner_cylinder_core
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
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
  let K  := localABPClosure v0
  obtain ⟨b, hbSmooth, hbOne, hbSupport⟩ :=
    exists_smooth_cutoff_tsupport_subset (isCompact_localABPClosure v0) hU hKU
  let ew  := exponentialConjugate rho (3 / 4) w
  let H  := fun z => exponentialTimeWeight rho (3 / 4) z * F z
  let g  := fun z => b z * ew z
  let G  := fun z => b z * H z
  let Bbar  := cutoffExtendCoefficient b B lam
  have hH : ContinuousOn H U := (contDiff_exponentialTimeWeight rho _).continuous.continuousOn.mul hF
  have hEW : ContDiffOn ℝ 2 ew U := contDiffOn_exponentialConjugate hw
  have hconj : IsParabolicSubsolutionOn B H ew (localABPInterior v0) := by
    intro z hz
    have hzK : z ∈ K := localABPInterior_subset_closure v0 hz
    have hzU  := hKU hzK
    rw [parabolicOperator_exponentialConjugate B
      (hw.contDiffAt (hU.mem_nhds hzU))]
    exact mul_le_mul_of_nonneg_left (hineq z hz)
      (exponentialTimeWeight_pos rho _ z).le
  have hg : ContDiff ℝ 2 g := contDiff_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hEW
  have hG : Continuous G := continuous_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hH
  have hBbar : IsContinuousCoefficient Bbar := continuous_coefficientAt_cutoffExtendCoefficient hU
      (hbSmooth.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hB
  have hgEq : g =ᶠ[𝓝ˢ K] ew := cutoff_mul_eventuallyEq hbOne
  have hGEq : G =ᶠ[𝓝ˢ K] H := cutoff_mul_eventuallyEq hbOne
  have hBbarEq : coefficientAt Bbar =ᶠ[𝓝ˢ K] coefficientAt B := coefficientAt_cutoffExtendCoefficient_eventuallyEq hbOne
  have hlocalSub : IsParabolicSubsolutionOn Bbar G g (localABPInterior v0) := by
    intro x hx
    have hxK : x ∈ K := localABPInterior_subset_closure v0 hx
    have hgx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hgEq
    have hGx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hGEq
    have hBx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hBbarEq
    have hoperator  :=
      parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq hBx hgx
    calc
      parabolicOperator Bbar g x = parabolicOperator B ew x := hoperator
      _ ≤ H x := hconj x hx
      _ = G x := (hGx.self_of_nhds).symm
  let a  := localABPAffine v0
  let Bhat  := pullbackCoefficient Bbar (3 / 4) v0 (1 / 2)
  let uhat  := pullbackScalar g (3 / 4) v0 (1 / 2)
  let fhat  := fun z => (1 / 2) ^ 2 * G (a z)
  have haCont : Continuous a := (contDiff_parabolicAffine _ v0 _).continuous
  have hBhat : IsContinuousCoefficient Bhat := hBbar.comp haCont
  have huhat : ContDiff ℝ 2 uhat := hg.comp (contDiff_parabolicAffine _ v0 _)
  have hfhat : Continuous fhat := continuous_const.mul (hG.comp haCont)
  have hLowHat : ∀ z ∈ closedParabolicCylinder 1 (0),
      lam • (1) ≤ coefficientAt Bhat z := by
    intro z hz
    have hzK : a z ∈ K := ⟨z, hz, rfl⟩
    have hBz := eventualEq_nhds_of_eventualEq_nhdsSet hzK hBbarEq
    change lam • (1) ≤ coefficientAt Bbar (a z)
    rw [hBz.self_of_nhds]
    exact hLow _ hzK
  have hsubHat : IsParabolicSubsolutionOn Bhat fhat uhat
      (parabolicInterior 1 (0)) := by
    intro z hz
    have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
    rw [show parabolicOperator Bhat uhat z =
        (1 / 2 : ℝ) ^ 2 * parabolicOperator Bbar g (a z) by
      exact parabolicOperator_pullbackScalar hg.contDiffAt]
    exact mul_le_mul_of_nonneg_left (hlocalSub _ hza) (sq_nonneg _)
  have hboundaryHat : ∀ z ∈ forwardParabolicBoundary 1 (0),
      uhat z ≤ 0 := by
    intro z hz
    have hza : a z ∈ localABPForwardBoundary v0 := ⟨z, hz, rfl⟩
    have hzaK : a z ∈ K := localABPForwardBoundary_subset_closure v0 hza
    have hgz := eventualEq_nhds_of_eventualEq_nhdsSet hzaK hgEq
    have hew : ew (a z) ≤ 0 := (exponentialConjugate_nonpos_iff rho _ w _).mpr
        (hboundary _ hza)
    change g (a z) ≤ 0
    rw [hgz.self_of_nhds]
    exact hew
  have hABPPoint := hABP (T := 1) (by norm_num) (by norm_num)
    _ Bhat fhat uhat hBhat hfhat huhat hLowHat hsubHat hboundaryHat
      _ referenceTarget_mem_closedParabolicCylinder
  have hmaxAE :
      (fun z => max (fhat z) 0) =ᵐ[volume.restrict (parabolicInterior 1 (0))]
        fun z => (1 / 2) ^ 2 * H (a z) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior 1 _)]
      with z hz
    have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
    have hzaK : a z ∈ K := localABPInterior_subset_closure v0 hza
    have hGz := eventualEq_nhds_of_eventualEq_nhdsSet hzaK hGEq
    have hHnonneg : 0 ≤ H (a z) := mul_nonneg (exponentialTimeWeight_pos rho _ _).le
        (hFnonneg _ hza)
    dsimp only [fhat]
    rw [hGz.self_of_nhds, max_eq_left]
    exact mul_nonneg (sq_nonneg _) hHnonneg
  have hnormMax :
      parabolicLpNormOn d (fun z => max (fhat z) 0)
          (parabolicInterior 1 (0)) =
        parabolicLpNormOn d (fun z => (1 / 2) ^ 2 * H (a z))
          (parabolicInterior 1 (0)) := congrArg ENNReal.toReal (eLpNorm_congr_ae hmaxAE)
  have hnorm := parabolicLpNormOn_pullback (d := d) (3 / 4) v0
    (by norm_num : 0 < (1 / 2 : ℝ)) H (parabolicInterior 1 (0))
  have hnorm' :
      parabolicLpNormOn d (fun z => (1 / 2) ^ 2 * H (a z))
          (parabolicInterior 1 (0)) =
        (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    simpa only [a, H, localABPAffine, localABPInterior] using hnorm
  have htargetK : (1, v0) ∈ K := localABPTarget_mem_closure v0
  have htargetg := eventualEq_nhds_of_eventualEq_nhdsSet htargetK hgEq
  have htargetWeight : exponentialTimeWeight rho (3 / 4) (1, v0) =
      Real.exp (rho / 4) := by
    rw [exponentialTimeWeight_apply]
    ring
  have hweighted :
      exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤
        C * (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    have huTarget : uhat (1, 0) = g (1, v0) := congrArg g (by
        simpa only [localABPAffine] using localABPAffine_referenceTarget v0)
    rw [huTarget, htargetg.self_of_nhds] at hABPPoint
    change exponentialTimeWeight rho _ _ * w _ ≤ _
      at hABPPoint
    rw [hnormMax, hnorm'] at hABPPoint
    simpa only [mul_assoc] using hABPPoint
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    w _ = Real.exp _ *
        (exponentialTimeWeight rho _ _ * w _) := by
      rw [htargetWeight, ← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp _ *
        (C * (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H _) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
    _ = C * (1 / 2) ^ (d / ((d : ℝ) + 1)) *
          Real.exp _ *
            parabolicLpNormOn d
              _
              _ := by
      dsimp only [H, exponentialTimeWeight]
      ring

/-- The local ABP consequence requiring lower ellipticity only on the compact
local cylinder used by its cutoff-and-pullback proof. -/
theorem exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
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
  obtain ⟨C, hC, hcore⟩ :=
    exists_local_abp_inner_cylinder_core d hd lam hlam
  exact ⟨C, hC, hcore⟩

end HypoellipticAleksandrov.Parabolic
