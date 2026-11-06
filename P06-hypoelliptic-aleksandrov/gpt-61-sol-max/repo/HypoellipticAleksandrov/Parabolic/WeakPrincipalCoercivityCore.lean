module

public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.LocalizedGradientDivergence
public import HypoellipticAleksandrov.Parabolic.SpatialPrincipalCoercivity
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import all HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
import all HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
import all HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict from HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
open private HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff from HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
open private HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_cutoff_compact from HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
section
open private HypoellipticAleksandrov.Parabolic.velocityGradient_velocityGradient from HypoellipticAleksandrov.Parabolic.WeakJetProduct
private alias _semanticProof_d1fb1bb268b0 := HypoellipticAleksandrov.Parabolic.velocityGradient_velocityGradient
end
section
open private HypoellipticAleksandrov.Parabolic.velocityHessian_compact from HypoellipticAleksandrov.Parabolic.WeakJetProduct
private alias _semanticProof_02a680b7b556 := HypoellipticAleksandrov.Parabolic.velocityHessian_compact
end


/-!
# Weak principal coercivity core

This module contains the proved localization, mollification, smooth coercivity,
and limit infrastructure used by the weak principal-coercivity conditions.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped ENNReal BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

/-- The scalar localized by multiplication with the cutoff. -/
def localizedScalar {d : ℕ} (b q : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => b z * q z

variable {d : ℕ}

variable (b q : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d)

/-- The gradient coordinate of the localized scalar. -/
def localizedGradient   (j : Fin d) : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => b z * QG z j + q z * velocityGradient b z j

/-- The ordered Hessian coordinate of the localized scalar. -/
def localizedHessian   (QH : TimeVelocity d → PDE.Mat d)
    (j i : Fin d) : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
  b z * QH z j i + velocityGradient b z i * QG z j +
    velocityGradient b z j * QG z i + q z * velocityHessian b z j i

private def mollifiedLocalizedScalar  (ε : ℝ)
    (b q : HypoellipticAleksandrov.Parabolic.ScalarField d) : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  SpacetimeMollifier.spacetimeMollification ε (localizedScalar b q)

private theorem memLp_top_of_ae_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f μ) (hC : ∀ᵐ x ∂μ, |f x| ≤ C) :
    MemLp f ∞ μ := by
  rw [MemLp, eLpNorm_exponent_top hf]
  exact (eLpNormEssSup_le_of_ae_bound hC).trans_lt ENNReal.ofReal_lt_top

variable {d : ℕ}

/-- Every coefficient entry is jointly measurable and essentially bounded by
the literal upper ellipticity constant on the product carrier. -/
private theorem coefficient_entry_memLp_top
     {lam Lam : ℝ} {S : HypoellipticAleksandrov.Parabolic.Region d}
    (A : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn S))
    (hlam : 0 < lam)
    (hAlower : ∀ z ∈ S, lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ S, A z ≤ Lam • (1 : PDE.Mat d))
    (hS : MeasurableSet S) (i j : Fin d) :
    AEStronglyMeasurable (fun z => A z i j) (timeVelocityVolumeOn S) ∧
      (∀ᵐ z ∂timeVelocityVolumeOn S, |A z i j| ≤ Lam) ∧
      MemLp (fun z => A z i j) ∞ (timeVelocityVolumeOn S) := by
  have hmeas  :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hAmeas)
  have hbound : ∀ᵐ z ∂timeVelocityVolumeOn S, |A z i j| ≤ Lam := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact abs_apply_le_of_loewner hlam (hAlower z hz) (hAupper z hz) i j
  exact ⟨hmeas, hbound, memLp_top_of_ae_abs_le _ _ hmeas hbound⟩




/-- The three literal rough principal-coercivity integrands are integrable on
the product cylinder under exactly the selected `L²` and cutoff hypotheses. -/
theorem WeakPrincipalCoercivityCore.targets_integrableOn
     (s₀ s₁ : ℝ) (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (lam Lam : ℝ) (A : TimeVelocity d → PDE.Mat d)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      A z ≤ Lam • (1 : PDE.Mat d))
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 *
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z)
      (Set.Ioo s₀ s₁ ×ˢ O)  ∧
    IntegrableOn (fun z => ζ z.1 * η z.2 ^ 2 *
      ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2)
      (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
    IntegrableOn (fun z => ζ z.1 * (tsupport η).indicator
      (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2)
      (Set.Ioo s₀ s₁ ×ˢ O) volume := by
  let S : HypoellipticAleksandrov.Parabolic.Region d := Set.Ioo s₀ s₁ ×ˢ O
  let μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  have hAij (i j : Fin d) : MemLp (fun z => A z i j) ∞ μ :=
    (coefficient_entry_memLp_top A hAmeas hlam hAlower hAupper hS i j).2.2

  have hpartialCont (k : Fin d) : Continuous (spatialPartial k η) := by
    unfold spatialPartial
    simpa using (hη.continuous_fderiv (by simp)).clm_apply continuous_const

  have hc₁ (k : Fin d) : MemLp (fun z : TimeVelocity d =>
      (-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) ∞ μ := by
    have hbase := _root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact (fun y => η y * spatialPartial k η y)
      (hη.continuous.mul (hpartialCont k)) hηCompact.mul_right
    convert hbase.const_smul (-2 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hηsqCompact : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηCompact.mul_right (f' := η)
  have hc₂ : MemLp (fun z : TimeVelocity d => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2)
      ∞ μ := by
    have hbase := _root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact (fun y => η y ^ 2) (hη.continuous.pow 2) hηsqCompact
    convert hbase.const_smul (-1 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

  have hprincipal : Integrable (fun z =>
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
        (ζ z.1 * WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z)) μ :=
    (show MemLp (fun z => ∑ i : Fin d, ∑ j : Fin d,
      A z i j * QH z j i) 2 μ by
        apply memLp_finset_sum Finset.univ
        intro i hi
        apply memLp_finset_sum Finset.univ
        intro j hj
        simpa only [mul_comm] using (hQH j i).mul' (hAij i j)).integrable_mul (by
        have hs (k : Fin d) : MemLp (fun z =>
            ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) * QG z k +
            ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QH z k k) 2 μ := by
          simpa only [Pi.add_def, mul_comm] using
            ((hQG k).fun_mul (hc₁ k)).add ((hQH k k).fun_mul hc₂)
        apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).mp
          (memLp_finset_sum Finset.univ fun k _ => hs k)
        · simp only [WeakGradientTimeEnergy.localizedGradientDivergence]
          rw [← Finset.sum_neg_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring)
  constructor
  · apply hprincipal.congr
    exact Filter.Eventually.of_forall fun z => by ring
  constructor
  · let c : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * η z.2 ^ 2
    have hc : MemLp c ∞ μ :=
      _root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict S ζ hζ.continuous hζCompact
        (fun y => η y ^ 2) (hη.continuous.pow 2) hηsqCompact
    have hi (k i : Fin d) : Integrable (fun z => c z * QH z k i * QH z k i) μ := by
      simpa only [Pi.mul_def, mul_comm] using
        ((hQH k i).fun_mul (r := 2) hc).integrable_mul (hQH k i)
    apply (integrable_finset_sum Finset.univ fun k _ =>
      integrable_finset_sum Finset.univ fun i _ => hi k i).congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [c, Finset.mul_sum]
      ring
  · obtain ⟨C, hC⟩ := hζ.continuous.bounded_above_of_compact_support hζCompact
    let c : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
      ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2
    have hcMeas : AEStronglyMeasurable c μ := by
      apply AEStronglyMeasurable.mul
      · exact (hζ.continuous.comp continuous_fst).aestronglyMeasurable
      · exact ((measurable_const.indicator (isClosed_tsupport η).measurableSet).comp
          continuous_snd.measurable).aestronglyMeasurable


    have hi (k : Fin d) : Integrable (fun z => c z * QG z k * QG z k) μ := by
      simpa only [Pi.mul_def, mul_comm] using
        ((hQG k).fun_mul (r := 2) (memLp_top_of_ae_abs_le c _ hcMeas (show ∀ᵐ z ∂μ, |c z| ≤ max C 0 by
            filter_upwards [] with z
            by_cases hz : z.2 ∈ tsupport η
            · rw [show c z = ζ z.1 by simp [c, hz]]

              exact (show |ζ z.1| ≤ C by
                  exact hC z.1).trans (le_max_left _ _)
            · have hc0 : c z = 0 := by simp [c, hz]
              rw [hc0, abs_zero]
              exact le_max_right _ _))).integrable_mul (hQG k)
    apply (integrable_finset_sum Finset.univ fun k _ => hi k).congr
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z.2 ∈ tsupport η
      · simp only [c, Set.indicator_of_mem hz]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      · simp [c, hz]

variable (b : HypoellipticAleksandrov.Parabolic.ScalarField d)

section
variable (hb : ContDiff ℝ PDE.smoothOrder b)




include hb in
private theorem velocityGradient_gradient

    (j i : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y j) z i =
      velocityHessian b z j i := (_semanticProof_d1fb1bb268b0 hb z)
end




private theorem velocityHessian_continuous
     (hb : ContDiff ℝ PDE.smoothOrder b) (j i : Fin d) :
    Continuous (fun z => velocityHessian b z j i) := by
  unfold velocityHessian

  simpa using (((contDiff_infty_iff_fderiv.mp hb).2).continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_compact
     (hb : HasCompactSupport b) (j i : Fin d) :
    HasCompactSupport (fun z => velocityHessian b z j i) := (_semanticProof_02a680b7b556 hb)

private theorem localized_spatial_jet_tsupport_subset
    (b q : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d) :
    tsupport (localizedScalar b q) ⊆ tsupport b ∧
      (∀ j : Fin d, tsupport (localizedGradient b q QG j) ⊆ tsupport b) ∧
      ∀ j i : Fin d, tsupport (localizedHessian b q QG QH j i) ⊆ tsupport b := by
  have close_support_subset (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (hf : Function.support f ⊆ tsupport b) : tsupport f ⊆ tsupport b := by
    simpa only [tsupport, closure_closure] using closure_mono hf
  constructor
  · exact close_support_subset _ fun z hz =>
      tsupport_mul_subset_left (subset_closure hz)
  constructor
  · intro j
    apply close_support_subset
    intro z hz
    by_contra hzb

    have hdb0 : velocityGradient b z j = 0 := by
      unfold velocityGradient
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    exact hz (by simp [localizedGradient, (image_eq_zero_of_notMem_tsupport hzb), hdb0])
  · intro j i
    apply close_support_subset
    intro z hz
    by_contra hzb

    have hdb0 (k : Fin d) : velocityGradient b z k = 0 := by
      unfold velocityGradient
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    have hddb0 : velocityHessian b z j i = 0 := by
      unfold velocityHessian
      have hsecond : fderiv ℝ (fderiv ℝ b) z = 0 := by
        rw [fderiv_of_notMem_tsupport ℝ]
        exact fun hmem => hzb (tsupport_fderiv_subset ℝ hmem)
      rw [hsecond]
      rfl
    exact hz (by simp [localizedHessian, (image_eq_zero_of_notMem_tsupport hzb), hdb0, hddb0])

variable {K : HypoellipticAleksandrov.Parabolic.Region d} {δ : ℝ}

/-- A plateau on a positive thickening is locally constant at every point of
the underlying compact carrier, so all selected first and mixed second
velocity derivatives vanish there. -/
private theorem plateau_spatial_value_derivatives

    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K))
    {z : TimeVelocity d} (hz : z ∈ Metric.thickening δ K) :
    b z = 1 ∧ (∀ i : Fin d, velocityGradient b z i = 0) ∧
      ∀ j i : Fin d, velocityHessian b z j i = 0 := by
  have hev : Filter.EventuallyEq (nhds z) b (1 ) := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds hz] with y hy
    exact hbOne (Metric.thickening_subset_cthickening δ K hy)

  have hdb : fderiv ℝ b z = 0 := by
    rw [hev.fderiv_eq]
    simp
  have hddb : fderiv ℝ (fderiv ℝ b) z = 0 := by

    rw [hev.fderiv.fderiv_eq]
    have hconst : fderiv ℝ (1 : HypoellipticAleksandrov.Parabolic.ScalarField d) = 0 := by
      funext y
      simp
    rw [hconst]
    simp
  refine ⟨hev.self_of_nhds, ?_, ?_⟩
  · intro i
    unfold velocityGradient
    rw [hdb]
    rfl
  · intro j i
    unfold velocityHessian
    rw [hddb]
    rfl

/-- The complete localized ordered spatial jet agrees literally with the
selected representatives on the compact plateau carrier. -/
private theorem localized_spatial_jet_eqOn_plateau

    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d) (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K)) :
    Set.EqOn (localizedScalar b q) q (Metric.thickening δ K) ∧
      (∀ j : Fin d, Set.EqOn (localizedGradient b q QG j)
        (fun z => QG z j) (Metric.thickening δ K)) ∧
      ∀ j i : Fin d, Set.EqOn (localizedHessian b q QG QH j i)
        (fun z => QH z j i) (Metric.thickening δ K) := by
  constructor
  · intro z hz
    obtain ⟨hbz, hbi, hbji⟩ := plateau_spatial_value_derivatives b hbOne hz
    simp [localizedScalar, hbz]
  constructor
  · intro j z hz
    obtain ⟨hbz, hbi, hbji⟩ := plateau_spatial_value_derivatives b hbOne hz
    simp [localizedGradient, hbz, hbi j]
  · intro j i z hz
    obtain ⟨hbz, hbi, hbji⟩ := plateau_spatial_value_derivatives b hbOne hz
    simp [localizedHessian, hbz, hbi, hbji j i]

/-- The temporal and spatial cutoff supports have one common smooth compact
plateau, on which the complete localized spatial jet recovers the selected
representatives exactly. -/
theorem WeakPrincipalCoercivityCore.exists_localized_spatial_jet_plateau
     (s₀ s₁ : ℝ) (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (η : PDE.ScalarField d) (hηCompact : HasCompactSupport η)
    (hηSupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (hζSupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ PDE.smoothOrder b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Set.Ioo s₀ s₁ ×ˢ O ∧
      Set.EqOn b 1
        (Metric.cthickening δ (tsupport ζ ×ˢ tsupport η)) ∧
      Set.EqOn (localizedScalar b q) q
        (Metric.thickening δ (tsupport ζ ×ˢ tsupport η)) ∧
      (∀ j : Fin d, Set.EqOn (localizedGradient b q QG j)
        (fun z => QG z j)
          (Metric.thickening δ (tsupport ζ ×ˢ tsupport η))) ∧
      ∀ j i : Fin d, Set.EqOn (localizedHessian b q QG QH j i)
        (fun z => QH z j i)
          (Metric.thickening δ (tsupport ζ ×ˢ tsupport η)) := by





  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset (isOpen_Ioo.prod hO) (hζCompact.isCompact.prod hηCompact.isCompact) (Set.prod_mono hζSupport hηSupport)
  rcases localized_spatial_jet_eqOn_plateau q QG QH b hbOne with
    ⟨hrEq, hriEq, hriiEq⟩
  exact ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne, hrEq, hriEq, hriiEq⟩

section
variable {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U) (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d) (hq : ParabolicMemLpOn U (2 ) q) (hQG : ∀ j : Fin d, ParabolicMemLpOn U (2 ) (fun z => QG z j)) (hQH : ∀ j i : Fin d, ParabolicMemLpOn U (2 ) (fun z => QH z j i)) (hqVelocity : ∀ j : Fin d, HasWeakVelocityPartialDerivOn U j q (fun z => QG z j)) (hQGVelocity : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn U i (fun z => QG z j) (fun z => QH z j i)) (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (hb : ContDiff ℝ PDE.smoothOrder b) (hbCompact : HasCompactSupport b) (hbSub : tsupport b ⊆ U)

include hU hq hQG hQH hqVelocity hQGVelocity hb hbCompact hbSub
/-- A single smooth compact cutoff localizes a complete ordered spatial weak
jet, globalizing every selected relation and every `L²` representative. -/
private theorem localized_ordered_spatial_jet_univ
      :
    (∀ j : Fin d, HasWeakVelocityPartialDerivOn Set.univ j
      (localizedScalar b q) (localizedGradient b q QG j)) ∧
      (∀ j i : Fin d, HasWeakVelocityPartialDerivOn Set.univ i
        (localizedGradient b q QG j) (localizedHessian b q QG QH j i)) ∧
      MemLp (localizedScalar b q) (2 )  ∧
      (∀ j : Fin d, MemLp (localizedGradient b q QG j) (2 ) ) ∧
      ∀ j i : Fin d, MemLp (localizedHessian b q QG QH j i)
        (2 )  := by
  have hbTop : ParabolicMemLpOn U ∞ b :=
    (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
  have hbiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityGradient b z i) :=
    ((_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff b hb i).continuous.memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_cutoff_compact b hbCompact i)).restrict U
  have hbijTop (j i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityHessian b z j i) :=
    ((velocityHessian_continuous b hb j i).memLp_of_hasCompactSupport
      (velocityHessian_compact b hbCompact j i)).restrict U

  have hri (j : Fin d) : ParabolicMemLpOn U 2 (localizedGradient b q QG j) := by
    apply (show ParabolicMemLpOn U 2 (fun z => b z * QG z j) from by
      simpa only [mul_comm] using (hQG j).mul' hbTop).add
    simpa only using hq.mul' (hbiTop j)
  have hrii (j i : Fin d) : ParabolicMemLpOn U 2
      (localizedHessian b q QG QH j i) := by
    have h1 : ParabolicMemLpOn U 2 (fun z => b z * QH z j i) := by
      simpa only [mul_comm] using (hQH j i).mul' hbTop



    exact ((h1.add (by
        simpa only [mul_comm] using (hQG j).mul' (hbiTop i))).add (by
        simpa only [mul_comm] using (hQG i).mul' (hbiTop j))).add ((MemLp.mul' hq (hbijTop j i)))
  have hrVelocity (j : Fin d) : HasWeakVelocityPartialDerivOn U j
      (localizedScalar b q) (localizedGradient b q QG j) := (hqVelocity j).mul_contDiff hb
        (hq.locallyIntegrableOn (by norm_num))
        ((hQG j).locallyIntegrableOn (by norm_num))
  have hriVelocity (j i : Fin d) : HasWeakVelocityPartialDerivOn U i
      (localizedGradient b q QG j) (localizedHessian b q QG QH j i) := by
    have hfirst := (hQGVelocity j i).mul_contDiff hb
      ((hQG j).locallyIntegrableOn (by norm_num))
      ((hQH j i).locallyIntegrableOn (by norm_num))

    have hsecond := (hqVelocity i).mul_contDiff (_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff b hb j)
      (hq.locallyIntegrableOn (by norm_num))
      ((hQG i).locallyIntegrableOn (by norm_num))




    have hadd := hfirst.add hsecond
      ((show ParabolicMemLpOn U 2 (fun z => b z * QG z j) by
          simpa only [mul_comm] using (hQG j).mul' hbTop).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U 2
        (fun z => b z * QH z j i + QG z j * velocityGradient b z i) by
              exact ((MemLp.add
          (Eq.mpr (id (congrArg (ParabolicMemLpOn U 2) (funext fun z => mul_comm (b z) (QH z j i))))
            (MemLp.mul' (hQH j i) hbTop))
          (MemLp.mul' (hQG j) (hbiTop i))))).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U 2
        (fun z => velocityGradient b z j * q z) by
          simpa only [mul_comm] using hq.mul' (hbiTop j)).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U 2
        (fun z => velocityGradient b z j * QG z i +
          q z * velocityGradient (fun y => velocityGradient b y j) z i) by


          exact (show ParabolicMemLpOn U 2
              (fun z => velocityGradient b z j * QG z i) by
              simpa only [mul_comm] using (hQG i).mul' (hbiTop j)).add (by
              simpa only [velocityGradient_gradient b hb j, mul_comm] using
                (hbijTop j i).mul' (r := 2) hq)).locallyIntegrableOn (by norm_num))
    convert hadd using 1 <;> funext z
    · simp only [localizedGradient]
      ring
    · simp_all [velocityGradient_gradient, localizedHessian] <;> ring
  rcases localized_spatial_jet_tsupport_subset b q QG QH with
    ⟨hrSupp, hriSupp, hriiSupp⟩
  have hrUniv (j : Fin d) := (hrVelocity j).univ_of_tsupport_subset hU
    (hrSupp.trans hbSub) ((hriSupp j).trans hbSub)
  have hriUniv (j i : Fin d) := (hriVelocity j i).univ_of_tsupport_subset hU
    ((hriSupp j).trans hbSub) ((hriiSupp j i).trans hbSub)
  have globalize {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hf : ParabolicMemLpOn U 2 f)
      (hs : tsupport f ⊆ U)  :=
    hf.memLp_of_support_subset hU.measurableSet (subset_tsupport f |>.trans hs)
  exact ⟨hrUniv, hriUniv, globalize (by
      change ParabolicMemLpOn U 2 (fun z => b z * q z)
      simpa only [mul_comm] using hq.mul' (r := 2) hbTop) (hrSupp.trans hbSub),
    fun j => globalize (hri j) ((hriSupp j).trans hbSub),
    fun j i => globalize (hrii j i) ((hriiSupp j i).trans hbSub)⟩

/-- One spacetime mollification of the localized scalar realizes every
selected first and ordered second velocity derivative, and all members of the
common family converge strongly in global `L²`. -/
private theorem common_mollifier_of_localized_ordered_spatial_jet
      :
    (∀ ε : ℝ, 0 < ε →
      ContDiff ℝ PDE.smoothOrder (mollifiedLocalizedScalar ε b q) ∧
      MemLp (mollifiedLocalizedScalar ε b q) (2 )  ∧
      (∀ j : Fin d, MemLp
        (SpacetimeMollifier.spacetimeMollification ε
          (localizedGradient b q QG j)) (2 ) ) ∧
      (∀ j i : Fin d, MemLp
        (SpacetimeMollifier.spacetimeMollification ε
          (localizedHessian b q QG QH j i)) (2 ) ) ∧
      (∀ z j, velocityGradient (mollifiedLocalizedScalar ε b q) z j =
        SpacetimeMollifier.spacetimeMollification ε
          (localizedGradient b q QG j) z) ∧
      ∀ z j i, velocityHessian (mollifiedLocalizedScalar ε b q) z j i =
        SpacetimeMollifier.spacetimeMollification ε
          (localizedHessian b q QG QH j i) z) ∧
    Filter.Tendsto (fun ε  => eLpNorm
      (mollifiedLocalizedScalar ε b q - localizedScalar b q) 2 )
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ j : Fin d, Filter.Tendsto (fun ε  => eLpNorm
      (SpacetimeMollifier.spacetimeMollification ε
        (localizedGradient b q QG j) - localizedGradient b q QG j) 2 )
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    ∀ j i : Fin d, Filter.Tendsto (fun ε  => eLpNorm
      (SpacetimeMollifier.spacetimeMollification ε
        (localizedHessian b q QG QH j i) - localizedHessian b q QG QH j i)
        2 ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rcases localized_ordered_spatial_jet_univ hU q QG QH hq hQG hQH
    hqVelocity hQGVelocity b hb hbCompact hbSub with
    ⟨hrVelocity, hriVelocity, hr, hri, hrii⟩
  have hmain (ε : ℝ) (hε : 0 < ε) :
      ContDiff ℝ PDE.smoothOrder (mollifiedLocalizedScalar ε b q) ∧
      MemLp (mollifiedLocalizedScalar ε b q) 2  ∧
      (∀ j : Fin d, MemLp
        (SpacetimeMollifier.spacetimeMollification ε
          (localizedGradient b q QG j)) 2 ) ∧
      (∀ j i : Fin d, MemLp
        (SpacetimeMollifier.spacetimeMollification ε
          (localizedHessian b q QG QH j i)) 2 ) ∧
      (∀ z j, velocityGradient (mollifiedLocalizedScalar ε b q) z j =
        SpacetimeMollifier.spacetimeMollification ε
          (localizedGradient b q QG j) z) ∧
      ∀ z j i, velocityHessian (mollifiedLocalizedScalar ε b q) z j i =
        SpacetimeMollifier.spacetimeMollification ε
          (localizedHessian b q QG QH j i) z := by
    have hsmooth := SpacetimeMollifier.contDiff_spacetimeMollification hε
      (localizedScalar b q) (hr.locallyIntegrable (by norm_num))
    have hfirst (j : Fin d) :=
      SpacetimeMollifier.velocityGradient_spacetimeMollification hε j
        (localizedScalar b q) (localizedGradient b q QG j)
        (hr.locallyIntegrable (by norm_num))
        ((hri j).locallyIntegrable (by norm_num)) (hrVelocity j)
    have hsecond (j i : Fin d) :=
      SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
        (localizedGradient b q QG j) (localizedHessian b q QG QH j i)
        ((hri j).locallyIntegrable (by norm_num))
        ((hrii j i).locallyIntegrable (by norm_num)) (hriVelocity j i)
    refine ⟨hsmooth,
      SpacetimeMollifierL2.spacetimeMollification_memLp hε _ hr,
      fun j => SpacetimeMollifierL2.spacetimeMollification_memLp hε _ (hri j),
      fun j i => SpacetimeMollifierL2.spacetimeMollification_memLp hε _ (hrii j i),
      ?_, ?_⟩
    · intro z j
      exact congrFun (hfirst j) z
    · intro z j i
      rw [← congrFun (hsecond j i) z]
      rw [← velocityGradient_gradient (mollifiedLocalizedScalar ε b q) hsmooth j i z]
      congr 1
      exact hfirst j
  refine ⟨hmain,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ hr,
    fun j => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ (hri j),
    fun j i => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _
      (hrii j i)⟩
end


section
variable (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ContDiff ℝ PDE.smoothOrder q) (r : ℝ) (y : PDE.Vec d)

include hq
private theorem spatialPartial_timeSlice
      (i : Fin d) :
    spatialPartial i (fun x => q (r, x)) y = velocityGradient q (r, y) i := by
  unfold spatialPartial velocityGradient
  have hslice := (hq.differentiable (by simp) (r, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right r y)
  change (fderiv ℝ (q ∘ Prod.mk r) y) (PDE.basisVec i) = _
  rw [hslice.fderiv]
  rfl

private theorem spatialSecond_timeSlice
      (j i : Fin d) :
    spatialSecond (fun x => q (r, x)) j i y = velocityHessian q (r, y) j i := by
  unfold spatialSecond
  rw [show spatialPartial j (fun x => q (r, x)) =
      fun x => velocityGradient q (r, x) j by
    funext x
    exact spatialPartial_timeSlice q hq r x j]
  rw [spatialPartial_timeSlice (fun z => velocityGradient q z j)
    (_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff q hq j)]
  exact velocityGradient_gradient q hq j i (r, y)
end


/-- The smooth spatial coercivity theorem applies to every time
slice of one common smooth spacetime scalar, with the supplied selected
derivative representatives substituted literally. -/
private theorem smooth_principal_coercivity_timeSlice
     (lam Lam M K : ℝ) (s₀ s₁ r : ℝ)
    (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d) (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hr : r ∈ Set.Ioo s₀ s₁)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      ∀ i j k : Fin d,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hq : ContDiff ℝ PDE.smoothOrder q)
    (hQG : ∀ z j, velocityGradient q z j = QG z j)
    (hQH : ∀ z j i, velocityHessian q z j i = QH z j i)
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K) :
    -( ∫ y in O, (∑ i : Fin d, ∑ j : Fin d,
        A (r, y) i j * QH (r, y) j i) *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y)) ≥
      lam / 2 * (∫ y in O, η y ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2) -
      principalCoercivityConstant d lam Lam M K *
        (∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2) := by

  have hsmooth : ContDiffOn ℝ 3 (fun y => q (r, y)) O :=
    (hq.comp (contDiff_const.prodMk contDiff_id)).contDiffOn.of_le (by
      norm_num)
  have hbase := smoothPrincipalIntegrationByParts_coercive lam Lam M K O hO
    (fun y => A (r, y)) (fun y => q (r, y)) η hlam hlamLam (hA r hr)
    (fun y hy => hAlower (r, y) ⟨hr, hy⟩)
    (fun y hy => hAupper (r, y) ⟨hr, hy⟩)
    (fun y hy => hAderiv (r, y) ⟨hr, hy⟩) hsmooth hη hηcompact hηsupport
    hηnonneg hηle hηderiv
  simpa only [spatialPartial_timeSlice q hq, spatialSecond_timeSlice q hq,
    hQG, hQH, WeakGradientTimeEnergy.localizedGradientDivergence] using hbase

section
variable (s₀ s₁ : ℝ) (O : PDE.VelocityRegion d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : IntegrableOn f (Set.Ioo s₀ s₁ ×ˢ O) volume)

include hf
/-- An integrable function on the literal product cylinder has the expected
iterated time--velocity integral. -/
private theorem integralOn_timeVelocity_prod
      :
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O, f z) =
      ∫ r in Set.Ioo s₀ s₁, ∫ y in O, f (r, y) := by
  change Integrable f (volume.restrict (Set.Ioo s₀ s₁ ×ˢ O)) at hf
  rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hf ⊢
  rw [integral_prod _ hf]

private theorem integrableOn_integral_timeVelocity_right
      :
    IntegrableOn (fun r => ∫ y in O, f (r, y)) (Set.Ioo s₀ s₁)  := by
  change Integrable f (volume.restrict (Set.Ioo s₀ s₁ ×ˢ O)) at hf
  rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left
end


private theorem indicator_gradient_slice
     (O : PDE.VelocityRegion d) (η : PDE.ScalarField d)
    (hηsupport : tsupport η ⊆ O) (r : ℝ)
    (QG : TimeVelocity d → PDE.Vec d) :
    (∫ y in O, (tsupport η).indicator
      (fun x => ∑ k : Fin d, QG (r, x) k ^ 2) y) =
      ∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2 := by
  rw [MeasureTheory.setIntegral_indicator (isClosed_tsupport η).measurableSet]
  rw [inter_eq_right.mpr hηsupport]

/-- Smooth spacetime principal coercivity obtained by weighting the exact
fixed-time theorem and integrating its slices over the literal cylinder. -/
private theorem smooth_principal_coercivity_spacetime
     (lam Lam M K : ℝ) (s₀ s₁ : ℝ)
    (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d) (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      ∀ i j k : Fin d,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hq : ContDiff ℝ PDE.smoothOrder q)
    (hQGid : ∀ z j, velocityGradient q z j = QG z j)
    (hQHid : ∀ z j i, velocityHessian q z j i = QH z j i)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζcompact : HasCompactSupport ζ) (hζnonneg : ∀ r, 0 ≤ ζ r) :
    -(∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z) ≥
      lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2) - principalCoercivityConstant d lam Lam M K *
      (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2) := by

  let S : HypoellipticAleksandrov.Parabolic.Region d := Set.Ioo s₀ s₁ ×ˢ O
  let L  := fun z => ζ z.1 *
    (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
    WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
  let E  := fun z =>
    ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
  let G : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 *
    (tsupport η).indicator (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2
  rcases WeakPrincipalCoercivityCore.targets_integrableOn s₀ s₁ O hO lam Lam A QG QH
    hAmeas hlam hAlower hAupper hQG hQH η hη hηcompact ζ hζ hζcompact with
    ⟨hL, hE, hG⟩
  have hR : IntegrableOn (fun z => lam / 2 * E z -
      principalCoercivityConstant d lam Lam M K * G z) S volume :=
    (hE.const_mul _).sub (hG.const_mul _)

  have hRo := integrableOn_integral_timeVelocity_right s₀ s₁ O
    (fun z => lam / 2 * E z - principalCoercivityConstant d lam Lam M K * G z) hR



  have hnegLo : IntegrableOn (fun r => -(∫ y in O, L (r, y)))
      (Set.Ioo s₀ s₁)  := (integrableOn_integral_timeVelocity_right s₀ s₁ O L hL).neg
  have hmono := integral_mono_ae hRo hnegLo (show _ by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, (by
          change Integrable E (volume.restrict S) at hE
          rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hE
          exact hE.prod_right_ae), (by
          change Integrable G (volume.restrict S) at hG
          rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hG
          exact hG.prod_right_ae)]
        with r hr hEr hGr
      have hs := smooth_principal_coercivity_timeSlice lam Lam M K s₀ s₁ r O hO
        A q QG QH hr hlam hlamLam hA hAlower hAupper hAderiv hq hQGid hQHid
        η hη hηcompact hηsupport hηnonneg hηle hηderiv
      have hw := mul_le_mul_of_nonneg_left hs (hζnonneg r)
      dsimp only [L, E, G]
      rw [integral_sub (hEr.const_mul _) (hGr.const_mul _),
        integral_const_mul, integral_const_mul]
      have hEs : (∫ y in O, ζ r * η y ^ 2 *
          ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2) =
          ζ r * (∫ y in O, η y ^ 2 *
            ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      have hGs : (∫ y in O, ζ r * (tsupport η).indicator
          (fun x => ∑ k : Fin d, QG (r, x) k ^ 2) y) =
          ζ r * (∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2) := by
        rw [integral_const_mul]
        exact congrArg (ζ r * ·) (indicator_gradient_slice O η hηsupport r QG)
      have hLs : (∫ y in O, (ζ r *
          ∑ i : Fin d, ∑ j : Fin d, A (r, y) i j * QH (r, y) j i) *
          WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y)) = ζ r * (∫ y in O,
            (∑ i : Fin d, ∑ j : Fin d, A (r, y) i j * QH (r, y) j i) *
            WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      rw [hEs, hGs, hLs]
      nlinarith)
  rw [integral_neg] at hmono
  change -(∫ z in S, L z) ≥
    lam / 2 * (∫ z in S, E z) -
      principalCoercivityConstant d lam Lam M K * (∫ z in S, G z)
  rw [integralOn_timeVelocity_prod s₀ s₁ O L hL]
  have hRalg : (∫ z in S, lam / 2 * E z -
      principalCoercivityConstant d lam Lam M K * G z) =
      lam / 2 * (∫ z in S, E z) -
        principalCoercivityConstant d lam Lam M K * (∫ z in S, G z) := by
    rw [integral_sub (hE.const_mul _) (hG.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [← hRalg, integralOn_timeVelocity_prod s₀ s₁ O _ hR]
  exact hmono

variable {l : Filter ℝ} (S : HypoellipticAleksandrov.Parabolic.Region d)

private theorem tendsto_eLpNorm_two_restrict_of_global

    (f : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (h : Filter.Tendsto (fun a => eLpNorm (f a - f₀) 2 ) l (nhds 0)) :
    Filter.Tendsto (fun a => eLpNorm (f a - f₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun a =>
      eLpNorm_mono_measure (f a - f₀) Measure.restrict_le_self)

private theorem tendsto_eLpNorm_two_fixed_mul

    (c : HypoellipticAleksandrov.Parabolic.ScalarField d) (f : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hc : MemLp c ∞ ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (h : Filter.Tendsto (fun a => eLpNorm (f a - f₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0)) :
    Filter.Tendsto (fun a => eLpNorm
      (fun z => c z * f a z - c z * f₀ z) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0) := HypoellipticAleksandrov.Analysis.tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two
    c f f₀ hc h

private theorem tendsto_integral_pairing_restrict

    (f g : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ g₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ᶠ a in l, MemLp (f a) 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf₀ : MemLp f₀ 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg₀ : MemLp g₀ 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hft : Filter.Tendsto (fun a => eLpNorm (f a - f₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0))
    (hgt : Filter.Tendsto (fun a => eLpNorm (g a - g₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0)) :
    Filter.Tendsto (fun a => ∫ z in S, f a z * g a z) l
      (nhds (∫ z in S, f₀ z * g₀ z)) := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    f g f₀ g₀ hf hg hf₀ hg₀ hft hgt

private theorem tendsto_integral_fixed_multipliers_pairing

    (c e : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f g : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ g₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hc : MemLp c ∞ ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (he : MemLp e ∞ ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf : ∀ᶠ a in l, MemLp (f a) 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf₀ : MemLp f₀ 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg₀ : MemLp g₀ 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hft : Filter.Tendsto (fun a => eLpNorm (f a - f₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0))
    (hgt : Filter.Tendsto (fun a => eLpNorm (g a - g₀) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (nhds 0)) :
    Filter.Tendsto (fun a => ∫ z in S, (c z * f a z) * (e z * g a z)) l
      (nhds (∫ z in S, (c z * f₀ z) * (e z * g₀ z))) := tendsto_integral_pairing_restrict S
    (fun a z => c z * f a z) (fun a z => e z * g a z)
    (fun z => c z * f₀ z) (fun z => e z * g₀ z)
    (by
        filter_upwards [hf] with a ha
        simpa only [mul_comm] using ha.mul' hc) (by
        filter_upwards [hg] with a ha
        simpa only [mul_comm] using ha.mul' he) (by
        simpa only [mul_comm] using hf₀.mul' hc) (by
        simpa only [mul_comm] using hg₀.mul' he)
    (tendsto_eLpNorm_two_fixed_mul S c f f₀ hc hft)
    (tendsto_eLpNorm_two_fixed_mul S e g g₀ he hgt)

variable (S : HypoellipticAleksandrov.Parabolic.Region d)

private theorem principal_limit_multipliers_memLp_top

    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ) :
    (∀ k : Fin d, MemLp (fun z : TimeVelocity d =>
      (-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) ∞
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) ∧
    MemLp (fun z : TimeVelocity d => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) ∧
    MemLp (fun z : TimeVelocity d => ζ z.1 * η z.2 ^ 2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) ∧
    MemLp (fun z : TimeVelocity d => ζ z.1 *
      (tsupport η).indicator (fun _ => (1 : ℝ)) z.2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) := by
  let sharedTerm_ed65ae6450 := (((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
  have hpartialCont (k : Fin d) : Continuous (spatialPartial k η) := by
    unfold spatialPartial
    simpa using (hη.continuous_fderiv (by simp)).clm_apply continuous_const


  have hfirst (k : Fin d) := _root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict S ζ
    hζ.continuous hζCompact (fun y => η y * spatialPartial k η y)
    (hη.continuous.mul (hpartialCont k)) hηCompact.mul_right
  have hsq := _root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.separated_multiplier_memLp_top_restrict S ζ hζ.continuous
    hζCompact (fun y => η y ^ 2) (hη.continuous.pow 2) (show HasCompactSupport (fun y => η y ^ 2) by
        simpa only [Pi.mul_def, pow_two] using hηCompact.mul_right (f' := η))

  obtain ⟨C, hC⟩ := hζ.continuous.bounded_above_of_compact_support hζCompact

  refine ⟨fun k => ?_, ?_, hsq, memLp_top_of_ae_abs_le _ _ (show AEStronglyMeasurable (fun z : TimeVelocity d => ζ z.1 *
      (tsupport η).indicator (fun _ => (1 : ℝ)) z.2)
      sharedTerm_ed65ae6450 by
      exact ((hζ.continuous.comp continuous_fst).aestronglyMeasurable.mul
        (((measurable_const.indicator (isClosed_tsupport η).measurableSet).comp
          continuous_snd.measurable).aestronglyMeasurable)).restrict) (show ∀ᵐ z ∂sharedTerm_ed65ae6450,
      |ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2| ≤ max C 0 by
      filter_upwards [] with z
      by_cases hz : z.2 ∈ tsupport η
      · simp only [Set.indicator_of_mem hz, mul_one]
        exact (show |ζ z.1| ≤ C by exact hC z.1).trans
          (le_max_left _ _)
      · simp [hz, le_max_right C 0])⟩
  · convert (hfirst k).const_smul (-2 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · convert hsq.const_smul (-1 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The three finite-coordinate integral expressions converge for the one
common mollification of the complete localized ordered spatial jet. -/
private theorem localized_principal_coordinate_integral_limits

    (lam Lam : ℝ) (A : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn S))
    (hlam : 0 < lam)
    (hAlower : ∀ z ∈ S, lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ S, A z ≤ Lam • (1 : PDE.Mat d))
    (hS : MeasurableSet S)
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ)
    (rG : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (rH : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hG : ∀ k, MemLp (rG k) 2 )
    (hH : ∀ j i, MemLp (rH j i) 2 ) :
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
      ((∫ z in S, (A z i j *
          SpacetimeMollifier.spacetimeMollification ε (rH j i) z) *
        (((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) *
          SpacetimeMollifier.spacetimeMollification ε (rG k) z)) +
       ∫ z in S, (A z i j *
          SpacetimeMollifier.spacetimeMollification ε (rH j i) z) *
        (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (rH k k) z)))
      (𝓝[>] 0) (𝓝 (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
      ((∫ z in S, (A z i j * rH j i z) *
        (((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) * rG k z)) +
       ∫ z in S, (A z i j * rH j i z) *
        (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rH k k z)))) ∧
    Filter.Tendsto (fun ε : ℝ => ∑ k : Fin d, ∑ i : Fin d,
      ∫ z in S, (ζ z.1 * η z.2 ^ 2 *
          SpacetimeMollifier.spacetimeMollification ε (rH k i) z) *
        SpacetimeMollifier.spacetimeMollification ε (rH k i) z)
      (𝓝[>] 0) (𝓝 (∑ k : Fin d, ∑ i : Fin d,
      ∫ z in S, (ζ z.1 * η z.2 ^ 2 * rH k i z) * rH k i z)) ∧
    Filter.Tendsto (fun ε  => ∑ k : Fin d,
      ∫ z in S, (ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2 *
          SpacetimeMollifier.spacetimeMollification ε (rG k) z) *
        SpacetimeMollifier.spacetimeMollification ε (rG k) z)
      (𝓝[>] 0) (𝓝 (∑ k : Fin d,
      ∫ z in S, (ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2 *
        rG k z) * rG k z)) := by
  let sharedTerm_a482cfc9d6 := (((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))


  have hmoll (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f 2 ) :
      ∀ᶠ ε : ℝ in (𝓝[>] 0), MemLp (SpacetimeMollifier.spacetimeMollification ε f) 2
        sharedTerm_a482cfc9d6 := by
    filter_upwards [(self_mem_nhdsWithin)] with ε hε
    exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε f hf).restrict S
  have hconv (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f 2 ) :=
    tendsto_eLpNorm_two_restrict_of_global S
      (fun ε => SpacetimeMollifier.spacetimeMollification ε f) f
      (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub f hf)
  rcases principal_limit_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hcE, hcG⟩
  have hAij (i j : Fin d) : MemLp (fun z => A z i j) ∞
      sharedTerm_a482cfc9d6 :=
    (coefficient_entry_memLp_top A hAmeas hlam hAlower hAupper hS i j).2.2
  have hone : MemLp (fun _ : TimeVelocity d => (1 : ℝ)) ∞
      sharedTerm_a482cfc9d6 :=
    memLp_top_of_ae_abs_le _ 1 measurable_const.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => by simp)
  constructor
  · apply tendsto_finset_sum Finset.univ
    intro i hi
    apply tendsto_finset_sum Finset.univ
    intro j hj
    apply tendsto_finset_sum Finset.univ
    intro k hk
    exact (tendsto_integral_fixed_multipliers_pairing S (fun z => A z i j)
      (fun z => (-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rH j i))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rG k))
      (rH j i) (rG k) (hAij i j) (hc₁ k) (hmoll _ (hH j i))
      (hmoll _ (hG k)) ((hH j i).restrict S) ((hG k).restrict S)
      (hconv _ (hH j i)) (hconv _ (hG k))).add
      (tendsto_integral_fixed_multipliers_pairing S (fun z => A z i j)
        (fun z => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2)
        (fun ε => SpacetimeMollifier.spacetimeMollification ε (rH j i))
        (fun ε => SpacetimeMollifier.spacetimeMollification ε (rH k k))
        (rH j i) (rH k k) (hAij i j) hc₂ (hmoll _ (hH j i))
        (hmoll _ (hH k k)) ((hH j i).restrict S) ((hH k k).restrict S)
        (hconv _ (hH j i)) (hconv _ (hH k k)))
  constructor
  · apply tendsto_finset_sum Finset.univ
    intro k hk
    apply tendsto_finset_sum Finset.univ
    intro i hi
    simpa only [one_mul] using tendsto_integral_fixed_multipliers_pairing S
      (fun z => ζ z.1 * η z.2 ^ 2) (fun _ => (1 ))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rH k i))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rH k i))
      (rH k i) (rH k i) hcE hone (hmoll _ (hH k i)) (hmoll _ (hH k i))
      ((hH k i).restrict S) ((hH k i).restrict S)
      (hconv _ (hH k i)) (hconv _ (hH k i))
  · apply tendsto_finset_sum Finset.univ
    intro k hk
    simpa only [one_mul] using tendsto_integral_fixed_multipliers_pairing S
      (fun z => ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2)
      (fun _ => (1 ))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rG k))
      (fun ε => SpacetimeMollifier.spacetimeMollification ε (rG k))
      (rG k) (rG k) hcG hone (hmoll _ (hG k)) (hmoll _ (hG k))
      ((hG k).restrict S) ((hG k).restrict S)
      (hconv _ (hG k)) (hconv _ (hG k))

private theorem sum_sum_sum_rotate  (f : Fin d → Fin d → Fin d → ℝ) :
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, f i j k) =
      ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, f i j k := (Trans.trans (Finset.sum_congr rfl fun i hi => Finset.sum_comm) Finset.sum_comm)

private theorem principal_coordinate_integral_algebra
     (S : HypoellipticAleksandrov.Parabolic.Region d) (A : TimeVelocity d → PDE.Mat d)
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d) (H : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hA : ∀ i j, MemLp (fun z => A z i j) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hG : ∀ k, MemLp (G k) 2 ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hH : ∀ j i, MemLp (H j i) 2
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) :
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
      ((∫ z in S, (A z i j * H j i z) * (((-2 : ℝ) * ζ z.1 *
          (η z.2 * spatialPartial k η z.2)) * G k z)) +
       ∫ z in S, (A z i j * H j i z) *
          (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * H k k z))) =
      ∫ z in S, ζ z.1 * (∑ i : Fin d, ∑ j : Fin d, A z i j * H j i z) *
        WeakGradientTimeEnergy.localizedGradientDivergence η
          (fun z k => G k z) (fun z j i => H j i z) z ∧
    (∑ k : Fin d, ∑ i : Fin d, ∫ z in S,
      (ζ z.1 * η z.2 ^ 2 * H k i z) * H k i z) =
      ∫ z in S, ζ z.1 * η z.2 ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, H k i z ^ 2 ∧
    (∑ k : Fin d, ∫ z in S, (ζ z.1 *
      (tsupport η).indicator (fun _ => (1 : ℝ)) z.2 * G k z) * G k z) =
      ∫ z in S, ζ z.1 * (tsupport η).indicator
        (fun y => ∑ k : Fin d, G k (z.1, y) ^ 2) z.2 := by
  let μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S
  rcases principal_limit_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hcE, hcG⟩
  have hP₁ (i j k : Fin d) : Integrable (fun z => (A z i j * H j i z) *
      (((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) * G k z)) μ := by
    simpa only [Pi.mul_def, mul_comm] using
      ((hH j i).mul' (r := 2) (hA i j)).integrable_mul
      ((hG k).mul' (r := 2) (hc₁ k))
  have hP₂ (i j k : Fin d) : Integrable (fun z => (A z i j * H j i z) *
      (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * H k k z)) μ := by
    simpa only [Pi.mul_def, mul_comm] using
      ((hH j i).mul' (r := 2) (hA i j)).integrable_mul
      ((hH k k).mul' (r := 2) hc₂)
  have hE (k i : Fin d) : Integrable (fun z =>
      (ζ z.1 * η z.2 ^ 2 * H k i z) * H k i z) μ := by
    simpa only [Pi.mul_def, mul_comm] using
      ((hH k i).mul' (r := 2) hcE).integrable_mul (hH k i)
  have hR (k : Fin d) : Integrable (fun z => (ζ z.1 *
      (tsupport η).indicator (fun _ => (1 : ℝ)) z.2 * G k z) * G k z) μ := by
    simpa only [Pi.mul_def, mul_comm] using
      ((hG k).mul' (r := 2) hcG).integrable_mul (hG k)
  constructor
  · calc
      _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∫ z,
          ((A z i j * H j i z) * (((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial k η z.2)) * G k z) +
          (A z i j * H j i z) *
            (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * H k k z)) ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [integral_add (hP₁ i j k) (hP₂ i j k)]
      _ = ∫ z, ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
          ((A z i j * H j i z) * (((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial k η z.2)) * G k z) +
          (A z i j * H j i z) *
            (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * H k k z)) ∂μ := (Trans.trans
  (Trans.trans
    (Finset.sum_congr rfl fun i hi =>
      Finset.sum_congr rfl fun j hj =>
        Eq.symm (integral_finset_sum Finset.univ fun k x => Integrable.add (hP₁ i j k) (hP₂ i j k)))
    (Finset.sum_congr rfl fun i hi =>
      Eq.symm
        (integral_finset_sum Finset.univ fun j x =>
          integrable_finset_sum Finset.univ fun k x => Integrable.add (hP₁ i j k) (hP₂ i j k))))
  (Eq.symm
    (integral_finset_sum Finset.univ fun i x =>
      integrable_finset_sum Finset.univ fun j x =>
        integrable_finset_sum Finset.univ fun k x => Integrable.add (hP₁ i j k) (hP₂ i j k))))
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp only [WeakGradientTimeEnergy.localizedGradientDivergence]
          rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
          simp_rw [Finset.mul_sum]
          ring_nf
          simp_rw [Finset.mul_sum]
          ring_nf
          simp_rw [Finset.sum_mul]
          ring_nf
          simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
          ring_nf
          exact sum_sum_sum_rotate _
  constructor
  · calc
      _ = ∫ z, ∑ k : Fin d, ∑ i : Fin d,
          (ζ z.1 * η z.2 ^ 2 * H k i z) * H k i z ∂μ := (Trans.trans (Finset.sum_congr rfl fun k hk => Eq.symm (integral_finset_sum Finset.univ fun i x => hE k i))
  (Eq.symm (integral_finset_sum Finset.univ fun k x => integrable_finset_sum Finset.univ fun i x => hE k i)))
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp_rw [Finset.mul_sum]
          ring
  · rw [← integral_finset_sum Finset.univ (fun k _ => hR k)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z.2 ∈ tsupport η
      · simp only [Set.indicator_of_mem hz, mul_one, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      · simp [hz]

/-- The raw localized weak jet satisfies the principal coercivity inequality,
before any plateau identities are used to recover the original representatives. -/
theorem WeakPrincipalCoercivityCore.localized_limit
     (lam Lam M K : ℝ) (s₀ s₁ : ℝ)
    (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d) (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (hqVelocity : ∀ j : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j))
    (hQGVelocity : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) i (fun z => QG z j) (fun z => QH z j i))
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (hb : ContDiff ℝ PDE.smoothOrder b)
    (hbCompact : HasCompactSupport b)
    (hbSub : tsupport b ⊆ Set.Ioo s₀ s₁ ×ˢ O)
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζcompact : HasCompactSupport ζ) (hζnonneg : ∀ r, 0 ≤ ζ r) :
    -(∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (∑ i : Fin d, ∑ j : Fin d, A z i j * localizedHessian b q QG QH j i z) *
        WeakGradientTimeEnergy.localizedGradientDivergence η
          (fun z j => localizedGradient b q QG j z)
          (fun z j i => localizedHessian b q QG QH j i z) z) ≥
      lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * η z.2 ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, localizedHessian b q QG QH k i z ^ 2) -
      principalCoercivityConstant d lam Lam M K *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, localizedGradient b q QG k (z.1, y) ^ 2) z.2) := by
  let S : HypoellipticAleksandrov.Parabolic.Region d := Set.Ioo s₀ s₁ ×ˢ O
  let rG  := (localizedGradient b q QG)
  let rH  :=
    (localizedHessian b q QG QH)
  rcases common_mollifier_of_localized_ordered_spatial_jet (isOpen_Ioo.prod hO)
      q QG QH hq hQG hQH hqVelocity hQGVelocity b hb hbCompact hbSub with
    ⟨hmoll, hscalarConv, hGconv, hHconv⟩
  have hglobal := localized_ordered_spatial_jet_univ (isOpen_Ioo.prod hO)
    q QG QH hq hQG hQH hqVelocity hQGVelocity b hb hbCompact hbSub
  rcases hglobal with ⟨_, _, hr, hrG, hrH⟩
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  have hAij (i j : Fin d) : MemLp (fun z => A z i j) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) :=
    (coefficient_entry_memLp_top A hAmeas hlam hAlower hAupper hS i j).2.2
  have halg := principal_coordinate_integral_algebra S A η hη hηcompact ζ hζ
    hζcompact rG rH hAij (fun k => (hrG k).restrict S)
      (fun j i => (hrH j i).restrict S)
  have hlimits := localized_principal_coordinate_integral_limits S lam Lam A
    hAmeas hlam hAlower hAupper hS η hη hηcompact ζ hζ hζcompact rG rH hrG hrH
  let P : ℝ → ℝ := fun ε => ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
    ((∫ z in S, (A z i j * SpacetimeMollifier.spacetimeMollification ε (rH j i) z) *
      (((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) *
        SpacetimeMollifier.spacetimeMollification ε (rG k) z)) +
     ∫ z in S, (A z i j * SpacetimeMollifier.spacetimeMollification ε (rH j i) z) *
      (((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
        SpacetimeMollifier.spacetimeMollification ε (rH k k) z))
  let E  := fun ε => ∑ k : Fin d, ∑ i : Fin d,
    ∫ z in S, (ζ z.1 * η z.2 ^ 2 *
      SpacetimeMollifier.spacetimeMollification ε (rH k i) z) *
      SpacetimeMollifier.spacetimeMollification ε (rH k i) z
  let G  := fun ε => ∑ k : Fin d,
    ∫ z in S, (ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2 *
      SpacetimeMollifier.spacetimeMollification ε (rG k) z) *
      SpacetimeMollifier.spacetimeMollification ε (rG k) z

  have hright := (hlimits.2.1.const_mul (lam / 2)).sub
    (hlimits.2.2.const_mul (principalCoercivityConstant d lam Lam M K))
  have hleft := hlimits.1.neg
  rw [halg.1] at hleft
  rw [halg.2.1, halg.2.2] at hright
  exact le_of_tendsto_of_tendsto hright hleft (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rcases hmoll ε hε with ⟨hqε, hqεLp, hGεLp, hHεLp, hGεid, hHεid⟩
      have hs := smooth_principal_coercivity_spacetime lam Lam M K s₀ s₁ O hO A
        (mollifiedLocalizedScalar ε b q)
        (fun z j => SpacetimeMollifier.spacetimeMollification ε (rG j) z)
        (fun z j i => SpacetimeMollifier.spacetimeMollification ε (rH j i) z)
        hAmeas hlam hlamLam hA hAlower hAupper hAderiv hqε hGεid hHεid
        (fun j => (hGεLp j).restrict S) (fun j i => (hHεLp j i).restrict S)
        η hη hηcompact hηsupport hηnonneg hηle hηderiv ζ hζ hζcompact hζnonneg
      have ha := principal_coordinate_integral_algebra S A η hη hηcompact ζ hζ hζcompact
        (fun j z => SpacetimeMollifier.spacetimeMollification ε (rG j) z)
        (fun j i z => SpacetimeMollifier.spacetimeMollification ε (rH j i) z)
        hAij (fun j => (hGεLp j).restrict S) (fun j i => (hHεLp j i).restrict S)
      simpa only [S, P, E, G, rG, rH, ha.1, ha.2.1, ha.2.2] using hs)

end HypoellipticAleksandrov.Parabolic
