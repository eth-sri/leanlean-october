module

public import HypoellipticAleksandrov.Parabolic.ABP
public import HypoellipticAleksandrov.Parabolic.ExponentialConjugation
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
import Aesop
import Batteries.Tactic.Alias
import Mathlib.Tactic.Ring
public import PDEFoundation.Calculus.RegularityOrder




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

variable {d : ℕ}

variable (v0 : PDE.Vec d)

/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine   : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)

/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior   : HypoellipticAleksandrov.Parabolic.Region d :=
  localABPAffine v0 '' parabolicInterior 1 0

/-- The compact closure of the local inner ABP cylinder. -/
def localABPClosure   : HypoellipticAleksandrov.Parabolic.Region d :=
  localABPAffine v0 '' closedParabolicCylinder 1 0

/-- The initial-plus-lateral, but not terminal, boundary of the local ABP
cylinder. -/
def localABPForwardBoundary   : HypoellipticAleksandrov.Parabolic.Region d :=
  localABPAffine v0 '' forwardParabolicBoundary 1 0

/-- The local ABP closure is compact. -/
theorem isCompact_localABPClosure   :
    IsCompact (localABPClosure v0) := by
  unfold localABPClosure localABPAffine
  exact (isCompact_closedParabolicCylinder 1 0).image
    (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous

/-- The local ABP interior is contained in its compact closure. -/
theorem localABPInterior_subset_closure   :
    localABPInterior v0 ⊆ localABPClosure v0 := by
  unfold localABPInterior localABPClosure
  exact Set.image_mono (parabolicInterior_subset_closedParabolicCylinder 1 0)

private theorem forwardParabolicBoundary_subset_closedParabolicCylinder_one
     :
    forwardParabolicBoundary 1 (0 : PDE.Vec d) ⊆
      closedParabolicCylinder 1 0 := by
  intro z hz
  rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
  · aesop
  · rcases z with ⟨t, v⟩
    rcases hlateral with ⟨ht0, ht1, hsphere⟩
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨ht0, ht1, (id (id (fun hsphere => Eq.le hsphere) hsphere))⟩

variable (v0 : PDE.Vec d)

/-- The local forward boundary is contained in the compact local ABP closure. -/
theorem localABPForwardBoundary_subset_closure   :
    localABPForwardBoundary v0 ⊆ localABPClosure v0 := by
  unfold localABPForwardBoundary localABPClosure
  exact Set.image_mono forwardParabolicBoundary_subset_closedParabolicCylinder_one

/-- The terminal centre is in the local ABP closure. -/
theorem localABPTarget_mem_closure   :
    (1, v0) ∈ localABPClosure v0 := by
  refine ⟨(1, 0), ?_, ?_⟩
  · exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
      change PDE.euclideanSqDist (0 : PDE.Vec d) 0 ≤ 1 ^ 2
      simp⟩
  · simp_all [localABPAffine, parabolicAffine] <;> ring

private theorem localABPAffine_referenceTarget   :
    localABPAffine v0 (1, 0) = (1, v0) := by
  simp_all [localABPAffine, parabolicAffine] <;> ring

private theorem referenceTarget_mem_closedParabolicCylinder  :
    (1, 0) ∈ closedParabolicCylinder 1 (0 : PDE.Vec d) := mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
    change PDE.euclideanSqDist (0 : PDE.Vec d) 0 ≤ 1 ^ 2
    simp⟩

private theorem eventualEq_nhds_of_eventualEq_nhdsSet {α : Type*}
    {β : Type*} [TopologicalSpace α] {K : Set α} {f g : α → β} {x : α}
    (hx : x ∈ K) (hfg : f =ᶠ[𝓝ˢ K] g) : f =ᶠ[𝓝 x] g :=
  (eventually_nhdsSet_iff_forall.mp hfg x hx)

variable (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam)

include hd hlam in
/-- Common proof of the local ABP consequences with ellipticity on the compact
cylinder actually used by the cutoff-and-pullback construction. -/
private theorem exists_local_abp_inner_cylinder_core
     :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : HypoellipticAleksandrov.Parabolic.Region d) (B : CoefficientField d)
        (w F : HypoellipticAleksandrov.Parabolic.ScalarField d) (v0 : PDE.Vec d) (rho : ℝ),
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
  let sharedTerm_c5aed8e0f7 := ((1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
  let sharedTerm_28a1c8c0b9 := ((by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (PDE.smoothOrder : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))
  let sharedTerm_7e43a1a2bc := ((parabolicInterior 1 (0 : PDE.Vec d)))
  let sharedTerm_a55316ead6 := ((1 / 2 : ℝ) ^ 2)
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



  have hg : ContDiff ℝ 2 g := by
    dsimp only [g]
    exact contDiff_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le sharedTerm_28a1c8c0b9) hbSupport (by
          dsimp only [ew]
          exact contDiffOn_exponentialConjugate hw)


  have hgEq : g =ᶠ[𝓝ˢ K] ew := by
    dsimp only [g]
    exact cutoff_mul_eventuallyEq hbOne
  have hGEq : G =ᶠ[𝓝ˢ K] H := by
    dsimp only [G]
    exact cutoff_mul_eventuallyEq hbOne
  have hBbarEq : coefficientAt Bbar =ᶠ[𝓝ˢ K] coefficientAt B := by
    dsimp only [Bbar]
    exact coefficientAt_cutoffExtendCoefficient_eventuallyEq hbOne

  let a  := localABPAffine v0
  let Bhat  := pullbackCoefficient Bbar (3 / 4) v0 (1 / 2)
  let uhat  := pullbackScalar g (3 / 4) v0 (1 / 2)
  let fhat  := fun z => sharedTerm_a55316ead6 * G (a z)

  have haCont : Continuous a := by
    dsimp only [a, localABPAffine]
    exact (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous






  have hABPPoint := hABP (T := 1) (by norm_num) (by norm_num)
    (0 ) Bhat fhat uhat (by
        dsimp only [Bhat]
        change Continuous ((coefficientAt Bbar) ∘ a)
        exact (show IsContinuousCoefficient Bbar by
            dsimp only [Bbar]
            exact continuous_coefficientAt_cutoffExtendCoefficient hU
              (hbSmooth.of_le sharedTerm_28a1c8c0b9) hbSupport hB).comp haCont) (by
        dsimp only [fhat]
        exact continuous_const.mul ((show Continuous G by
            dsimp only [G]
            exact continuous_cutoff_mul_of_tsupport_subset hU
              (hbSmooth.of_le sharedTerm_28a1c8c0b9) hbSupport (by
                  dsimp only [H]
                  exact (contDiff_exponentialTimeWeight rho (3 / 4)).continuous.continuousOn.mul hF)).comp haCont)) (by
        dsimp only [uhat]
        change ContDiff ℝ 2 (g ∘ a)
        exact hg.comp (contDiff_parabolicAffine (3 / 4) v0 (1 / 2))) (by
        intro z hz
        have hzK : a z ∈ K := ⟨z, hz, rfl⟩

        change lam • (1 : PDE.Mat d) ≤ coefficientAt Bbar (a z)
        rw [(eventualEq_nhds_of_eventualEq_nhdsSet hzK hBbarEq).self_of_nhds]
        exact hLow (a z) hzK) (by
        intro z hz
        have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
        change parabolicOperator Bhat uhat z ≤ sharedTerm_a55316ead6 * G (a z)
        rw [show parabolicOperator Bhat uhat z =
            sharedTerm_a55316ead6 * parabolicOperator Bbar g (a z) by exact (id (parabolicOperator_pullbackScalar (ContDiff.contDiffAt hg)))]
        exact mul_le_mul_of_nonneg_left ((show IsParabolicSubsolutionOn Bbar G g (localABPInterior v0) by
            intro x hx
            have hxK  := localABPInterior_subset_closure v0 hx




            calc
              parabolicOperator Bbar g x = parabolicOperator B ew x := (parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq (eventualEq_nhds_of_eventualEq_nhdsSet hxK hBbarEq) (eventualEq_nhds_of_eventualEq_nhdsSet hxK hgEq))
              _ ≤ H x := (show IsParabolicSubsolutionOn B H ew (localABPInterior v0) by
                  intro z hz
                  have hzK  := localABPInterior_subset_closure v0 hz

                  dsimp only [H, ew]
                  rw [parabolicOperator_exponentialConjugate B
                    (hw.contDiffAt (hU.mem_nhds (hKU hzK)))]
                  exact mul_le_mul_of_nonneg_left (hineq z hz)
                    (exponentialTimeWeight_pos rho (3 / 4) z).le) x hx
              _ = G x := ((eventualEq_nhds_of_eventualEq_nhdsSet hxK hGEq).self_of_nhds).symm) (a z) hza) (sq_nonneg (1 / 2 : ℝ))) (by
        intro z hz
        have hza : a z ∈ localABPForwardBoundary v0 := ⟨z, hz, rfl⟩



        change uhat z ≤ 0
        change g (a z) ≤ 0
        rw [(eventualEq_nhds_of_eventualEq_nhdsSet (localABPForwardBoundary_subset_closure v0 hza) hgEq).self_of_nhds]
        exact (by
            dsimp only [ew]
            exact (exponentialConjugate_nonpos_iff rho (3 / 4) w (a z)).mpr
              (hboundary (a z) hza)))
      (1, 0) referenceTarget_mem_closedParabolicCylinder

  have hnormMax :
      parabolicLpNormOn d (fun z => max (fhat z) 0)
          sharedTerm_7e43a1a2bc =
        parabolicLpNormOn d (fun z => sharedTerm_a55316ead6 * H (a z))
          sharedTerm_7e43a1a2bc := by
    unfold parabolicLpNormOn parabolicELpNormOn
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (by
        filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior 1 (0 : PDE.Vec d))]
          with z hz
        have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩



        dsimp only [fhat]
        rw [(eventualEq_nhds_of_eventualEq_nhdsSet (localABPInterior_subset_closure v0 hza) hGEq).self_of_nhds, max_eq_left]
        exact mul_nonneg (sq_nonneg (1 / 2 : ℝ)) (by
            dsimp only [H]
            exact mul_nonneg (exponentialTimeWeight_pos rho (3 / 4) (a z)).le
              (hFnonneg (a z) hza))))
  have hnorm := parabolicLpNormOn_pullback (d := d) (3 / 4) v0
    (by norm_num : 0 < (1 / 2 : ℝ)) H sharedTerm_7e43a1a2bc
  have hnorm' :
      parabolicLpNormOn d (fun z => sharedTerm_a55316ead6 * H (a z))
          sharedTerm_7e43a1a2bc =
        sharedTerm_c5aed8e0f7 *
          parabolicLpNormOn d H (localABPInterior v0) := by
    exact hnorm

  have htargetg := eventualEq_nhds_of_eventualEq_nhdsSet (by
      dsimp only [K]
      exact localABPTarget_mem_closure v0) hgEq
  have htargetWeight : exponentialTimeWeight rho (3 / 4) (1, v0) =
      Real.exp (rho / 4) := by
    rw [exponentialTimeWeight_apply]
    congr 1
    ring

  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    w (1, v0) = Real.exp (-rho / 4) *
        (exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0)) := by
      rw [htargetWeight, ← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (-rho / 4) *
        (C * sharedTerm_c5aed8e0f7 *
          parabolicLpNormOn d H (localABPInterior v0)) :=
      mul_le_mul_of_nonneg_left (by
          have huTarget : uhat (1, 0) = g (1, v0) := by
            change g (parabolicAffine (3 / 4) v0 (1 / 2) (1, 0)) = g (1, v0)
            exact congrArg g (localABPAffine_referenceTarget v0)
          change uhat (1, 0) ≤ _ at hABPPoint
          rw [huTarget, htargetg.self_of_nhds] at hABPPoint
          change exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤ _
            at hABPPoint
          rw [hnormMax, hnorm'] at hABPPoint
          simpa only [mul_assoc] using hABPPoint) (Real.exp_pos _).le
    _ = C * sharedTerm_c5aed8e0f7 *
          Real.exp (-rho / 4) *
            parabolicLpNormOn d
              (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
              (localABPInterior v0) := by
      dsimp only [H, exponentialTimeWeight]
      ring

/-- The local ABP consequence requiring lower ellipticity only on the compact
local cylinder used by its cutoff-and-pullback proof. -/
alias exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure := _root_.HypoellipticAleksandrov.Parabolic.exists_local_abp_inner_cylinder_core


end HypoellipticAleksandrov.Parabolic
