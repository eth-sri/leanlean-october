module

public import HypoellipticAleksandrov.Parabolic.WeakJetLocalization
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.WeightedTimeVelocityL2
public import HypoellipticAleksandrov.Parabolic.SpatialPrincipalCoercivity
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence

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

open WeakGradientTimeEnergy

private def mollifiedLocalizedScalar {d : ℕ} (ε : ℝ)
    (b q : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  SpacetimeMollifier.spacetimeMollification ε (localizedScalar b q)

private theorem memLp_top_of_ae_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f μ) (hC : ∀ᵐ x ∂μ, |f x| ≤ C) :
    MemLp f ∞ μ := by
  rw [MemLp, eLpNorm_exponent_top hf]
  exact (eLpNormEssSup_le_of_ae_bound hC).trans_lt ENNReal.ofReal_lt_top

/-- Every coefficient entry is jointly measurable and essentially bounded by
the literal upper ellipticity constant on the product carrier. -/
private theorem coefficient_entry_memLp_top
    {d : ℕ} {lam Lam : ℝ} {S : Set (TimeVelocity d)}
    (A : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn S))
    (hlam : 0 < lam)
    (hAlower : ∀ z ∈ S, lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ S, A z ≤ Lam • (1 : PDE.Mat d))
    (hS : MeasurableSet S) (i j : Fin d) :
    AEStronglyMeasurable (fun z => A z i j) (timeVelocityVolumeOn S) ∧
      (∀ᵐ z ∂timeVelocityVolumeOn S, |A z i j| ≤ Lam) ∧
      MemLp (fun z => A z i j) ∞ (timeVelocityVolumeOn S) := by
  have hmeas :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hAmeas)
  have hbound : ∀ᵐ z ∂timeVelocityVolumeOn S, |A z i j| ≤ Lam := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact abs_apply_le_of_loewner hlam (hAlower z hz) (hAupper z hz) i j
  exact ⟨hmeas, hbound, memLp_top_of_ae_abs_le _ _ hmeas hbound⟩

section
variable {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
include hO

/-- The three literal rough principal-coercivity integrands are integrable on
the product cylinder under exactly the selected `L²` and cutoff hypotheses. -/
theorem WeakPrincipalCoercivityCore.targets_integrableOn
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
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 *
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z)
      (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
    IntegrableOn (fun z => ζ z.1 * η z.2 ^ 2 *
      ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2)
      (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
    IntegrableOn (fun z => ζ z.1 * (tsupport η).indicator
      (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2)
      (Set.Ioo s₀ s₁ ×ˢ O) volume := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let μ := (volume : Measure (TimeVelocity d)).restrict S
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  have hAij (i j : Fin d) : MemLp (fun z => A z i j) ∞ μ :=
    (coefficient_entry_memLp_top A hAmeas hlam hAlower hAupper hS i j).2.2
  have hP : MemLp (fun z => ∑ i : Fin d, ∑ j : Fin d,
      A z i j * QH z j i) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i hi
    apply memLp_finset_sum Finset.univ
    intro j hj
    simpa only [mul_comm] using (hQH j i).mul' (hAij i j)
  have hD := localizedGradientDivergence_memLp S QG QH hQG (fun k => hQH k k)
    η hη hηCompact ζ hζ hζCompact
  obtain ⟨-, -, hE, -⟩ := energy_weights_memLp_top S η hη hηCompact ζ hζ hζCompact
  have hG := supportIndicator_memLp_top S η hζ.continuous hζCompact
  refine ⟨(hP.integrable_mul hD).congr (ae_of_all _ fun _ => by simp [Pi.mul_apply]; ring), ?_, ?_⟩
  · have h := Analysis.integrable_weighted_sum_sq (ι := Fin d × Fin d) hE (fun ij => hQH ij.1 ij.2)
    simpa only [Fintype.sum_prod_type, IntegrableOn, timeVelocityVolumeOn, S] using h
  · refine (Analysis.integrable_weighted_sum_sq hG hQG).congr (ae_of_all _ fun z => ?_)
    by_cases hz : z.2 ∈ tsupport η <;> simp [hz]

/-- The temporal and spatial cutoff supports have one common smooth compact
plateau, on which the complete localized spatial jet recovers the selected
representatives exactly. -/
theorem WeakPrincipalCoercivityCore.exists_localized_spatial_jet_plateau
    (q : TimeVelocity d → ℝ) (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (η : PDE.Vec d → ℝ) (hηCompact : HasCompactSupport η)
    (hηSupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (hζSupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
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
  obtain ⟨δ, hδ, b, hb, hc, hs, h1⟩ := exists_contDiff_one_on_cthickening_tsupport_subset
    (isOpen_Ioo.prod hO) (hζCompact.isCompact.prod hηCompact.isCompact) (Set.prod_mono hζSupport hηSupport)
  obtain ⟨hr, _, hG, hH⟩ := localized_jet_eqOn_plateau q 0 QG QH h1
  exact ⟨δ, hδ, b, hb, hc, hs, h1, hr, hG, hH⟩

end

section
variable {d : ℕ} (q : TimeVelocity d → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (r : ℝ) (y : PDE.Vec d)
include hq

private theorem spatialPartial_timeSlice (i : Fin d) :
    spatialPartial i (fun x => q (r, x)) y = velocityGradient q (r, y) i := by
  unfold spatialPartial velocityGradient
  have hslice := (hq.differentiable (by simp) (r, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right r y)
  change (fderiv ℝ (q ∘ Prod.mk r) y) (PDE.basisVec i) = _
  rw [hslice.fderiv]
  rfl

private theorem spatialSecond_timeSlice (j i : Fin d) :
    spatialSecond (fun x => q (r, x)) j i y = velocityHessian q (r, y) j i := by
  unfold spatialSecond
  rw [show spatialPartial j (fun x => q (r, x)) =
      fun x => velocityGradient q (r, x) j by
    funext x
    exact spatialPartial_timeSlice q hq r x j]
  rw [spatialPartial_timeSlice (fun z => velocityGradient q z j)
    (velocityGradient_contDiff (i := j) hq)]
  exact velocityGradient_velocityGradient hq (r, y)

end

/-- The smooth spatial coercivity theorem applies to every time
slice of one common smooth spacetime scalar, with the supplied selected
derivative representatives substituted literally. -/
private theorem smooth_principal_coercivity_timeSlice
    {d : ℕ} (lam Lam M K : ℝ) (s₀ s₁ r : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
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
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hQG : ∀ z j, velocityGradient q z j = QG z j)
    (hQH : ∀ z j i, velocityHessian q z j i = QH z j i)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K) :
    -( ∫ y in O, (∑ i : Fin d, ∑ j : Fin d,
        A (r, y) i j * QH (r, y) j i) *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y) ∂volume) ≥
      lam / 2 * (∫ y in O, η y ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2 ∂volume) -
      principalCoercivityConstant d lam Lam M K *
        (∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2 ∂volume) := by
  have hsliceSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => q (r, y)) :=
    hq.comp (contDiff_const.prodMk contDiff_id)
  have hsmooth : ContDiffOn ℝ 3 (fun y => q (r, y)) O :=
    hsliceSmooth.contDiffOn.of_le (by
      change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hbase := smoothPrincipalIntegrationByParts_coercive lam Lam M K O hO
    (fun y => A (r, y)) (fun y => q (r, y)) η hlam hlamLam (hA r hr)
    (fun y hy => hAlower (r, y) ⟨hr, hy⟩)
    (fun y hy => hAupper (r, y) ⟨hr, hy⟩)
    (fun y hy => hAderiv (r, y) ⟨hr, hy⟩) hsmooth hη hηcompact hηsupport
    hηnonneg hηle hηderiv
  simpa only [spatialPartial_timeSlice q hq, spatialSecond_timeSlice q hq,
    hQG, hQH, WeakGradientTimeEnergy.localizedGradientDivergence] using hbase

section
variable {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (f : TimeVelocity d → ℝ)
  (hf : IntegrableOn f (Set.Ioo s₀ s₁ ×ˢ O) volume)
include hf

/-- An integrable function on the literal product cylinder has the expected
iterated time--velocity integral. -/
private theorem integralOn_timeVelocity_prod :
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O, f z ∂volume) =
      ∫ r in Set.Ioo s₀ s₁, ∫ y in O, f (r, y) ∂volume ∂volume := by
  change Integrable f
    ((volume : Measure (TimeVelocity d)).restrict (Set.Ioo s₀ s₁ ×ˢ O)) at hf
  rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hf ⊢
  rw [integral_prod _ hf]

private theorem integrableOn_integral_timeVelocity_right :
    IntegrableOn (fun r => ∫ y in O, f (r, y) ∂volume) (Set.Ioo s₀ s₁) volume := by
  change Integrable f
    ((volume : Measure (TimeVelocity d)).restrict (Set.Ioo s₀ s₁ ×ˢ O)) at hf
  rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left

end

private theorem indicator_gradient_slice
    {d : ℕ} (O : Set (PDE.Vec d)) (η : PDE.Vec d → ℝ)
    (hηsupport : tsupport η ⊆ O) (r : ℝ)
    (QG : TimeVelocity d → PDE.Vec d) :
    (∫ y in O, (tsupport η).indicator
      (fun x => ∑ k : Fin d, QG (r, x) k ^ 2) y ∂volume) =
      ∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2 ∂volume := by
  rw [MeasureTheory.setIntegral_indicator (isClosed_tsupport η).measurableSet, inter_eq_right.mpr hηsupport]

section
variable {d : ℕ} (lam Lam M K : ℝ) (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
  (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ) (QG : TimeVelocity d → PDE.Vec d)
  (QH : TimeVelocity d → PDE.Mat d)
  (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))) (hlam : 0 < lam)
  (hlamLam : lam ≤ Lam)
  (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
  (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, lam • (1 : PDE.Mat d) ≤ A z)
  (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, A z ≤ Lam • (1 : PDE.Mat d))
  (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d, |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
include hO hAmeas hlam hlamLam hA hAlower hAupper hAderiv

/-- Smooth spacetime principal coercivity obtained by weighting the exact
fixed-time theorem and integrating its slices over the literal cylinder. -/
private theorem smooth_principal_coercivity_spacetime
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hQGid : ∀ z j, velocityGradient q z j = QG z j)
    (hQHid : ∀ z j i, velocityHessian q z j i = QH z j i)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ) (hζnonneg : ∀ r, 0 ≤ ζ r) :
    -(∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume) ≥
      lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
        ∂volume) - principalCoercivityConstant d lam Lam M K *
      (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2 ∂volume) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let L : TimeVelocity d → ℝ := fun z => ζ z.1 *
    (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
    WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
  let E : TimeVelocity d → ℝ := fun z =>
    ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
  let G : TimeVelocity d → ℝ := fun z => ζ z.1 *
    (tsupport η).indicator (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2
  rcases WeakPrincipalCoercivityCore.targets_integrableOn s₀ s₁ O hO lam Lam A QG QH
    hAmeas hlam hAlower hAupper hQG hQH η hη hηcompact ζ hζ hζcompact with
    ⟨hL, hE, hG⟩
  have hR : IntegrableOn (fun z => lam / 2 * E z -
      principalCoercivityConstant d lam Lam M K * G z) S volume :=
    (hE.const_mul _).sub (hG.const_mul _)
  have hLo := integrableOn_integral_timeVelocity_right s₀ s₁ O L hL
  have hRo := integrableOn_integral_timeVelocity_right s₀ s₁ O
    (fun z => lam / 2 * E z - principalCoercivityConstant d lam Lam M K * G z) hR
  have hEsections : ∀ᵐ r ∂(volume.restrict (Set.Ioo s₀ s₁)),
      Integrable (fun y => E (r, y)) (volume.restrict O) := by
    change Integrable E (volume.restrict S) at hE
    rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hE
    exact hE.prod_right_ae
  have hGsections : ∀ᵐ r ∂(volume.restrict (Set.Ioo s₀ s₁)),
      Integrable (fun y => G (r, y)) (volume.restrict O) := by
    change Integrable G (volume.restrict S) at hG
    rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hG
    exact hG.prod_right_ae
  have hpoint : ∀ᵐ r ∂(volume.restrict (Set.Ioo s₀ s₁)),
      (∫ y in O, lam / 2 * E (r, y) -
        principalCoercivityConstant d lam Lam M K * G (r, y) ∂volume) ≤
      -(∫ y in O, L (r, y) ∂volume) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hEsections, hGsections]
      with r hr hEr hGr
    have hs := smooth_principal_coercivity_timeSlice lam Lam M K s₀ s₁ r O hO
      A q QG QH hr hlam hlamLam hA hAlower hAupper hAderiv hq hQGid hQHid
      η hη hηcompact hηsupport hηnonneg hηle hηderiv
    have hw := mul_le_mul_of_nonneg_left hs (hζnonneg r)
    dsimp only [L, E, G]
    rw [integral_sub (hEr.const_mul _) (hGr.const_mul _),
      integral_const_mul, integral_const_mul]
    have hEs : (∫ y in O, ζ r * η y ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2 ∂volume) =
        ζ r * (∫ y in O, η y ^ 2 *
          ∑ k : Fin d, ∑ i : Fin d, QH (r, y) k i ^ 2 ∂volume) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring
    have hGs : (∫ y in O, ζ r * (tsupport η).indicator
        (fun x => ∑ k : Fin d, QG (r, x) k ^ 2) y ∂volume) =
        ζ r * (∫ y in tsupport η, ∑ k : Fin d, QG (r, y) k ^ 2
          ∂volume) := by
      rw [integral_const_mul]
      exact congrArg (ζ r * ·) (indicator_gradient_slice O η hηsupport r QG)
    have hLs : (∫ y in O, (ζ r *
        ∑ i : Fin d, ∑ j : Fin d, A (r, y) i j * QH (r, y) j i) *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y)
        ∂volume) = ζ r * (∫ y in O,
          (∑ i : Fin d, ∑ j : Fin d, A (r, y) i j * QH (r, y) j i) *
          WeakGradientTimeEnergy.localizedGradientDivergence η QG QH (r, y)
          ∂volume) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring
    rw [hEs, hGs, hLs]
    nlinarith
  have hnegLo : IntegrableOn (fun r => -(∫ y in O, L (r, y) ∂volume))
      (Set.Ioo s₀ s₁) volume := hLo.neg
  have hmono := integral_mono_ae hRo hnegLo hpoint
  rw [integral_neg] at hmono
  change -(∫ z in S, L z ∂volume) ≥
    lam / 2 * (∫ z in S, E z ∂volume) -
      principalCoercivityConstant d lam Lam M K * (∫ z in S, G z ∂volume)
  rw [integralOn_timeVelocity_prod s₀ s₁ O L hL]
  have hRalg : (∫ z in S, lam / 2 * E z -
      principalCoercivityConstant d lam Lam M K * G z ∂volume) =
      lam / 2 * (∫ z in S, E z ∂volume) -
        principalCoercivityConstant d lam Lam M K * (∫ z in S, G z ∂volume) := by
    rw [integral_sub (hE.const_mul _) (hG.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [← hRalg, integralOn_timeVelocity_prod s₀ s₁ O _ hR]
  exact hmono

/-- The raw localized weak jet satisfies the principal coercivity inequality,
before any plateau identities are used to recover the original representatives. -/
theorem WeakPrincipalCoercivityCore.localized_limit
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (hqVelocity : ∀ j : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j))
    (hQGVelocity : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) i (fun z => QG z j) (fun z => QH z j i))
    (b : TimeVelocity d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b)
    (hbSub : tsupport b ⊆ Set.Ioo s₀ s₁ ×ˢ O)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ) (hζnonneg : ∀ r, 0 ≤ ζ r) :
    -(∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (∑ i : Fin d, ∑ j : Fin d, A z i j * localizedHessian b q QG QH j i z) *
        WeakGradientTimeEnergy.localizedGradientDivergence η
          (fun z j => localizedGradient b q QG j z)
          (fun z j i => localizedHessian b q QG QH j i z) z ∂volume) ≥
      lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * η z.2 ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, localizedHessian b q QG QH k i z ^ 2 ∂volume) -
      principalCoercivityConstant d lam Lam M K *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, localizedGradient b q QG k (z.1, y) ^ 2) z.2 ∂volume) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let rG : Fin d → TimeVelocity d → ℝ := fun j => localizedGradient b q QG j
  let rH : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun j i => localizedHessian b q QG QH j i
  obtain ⟨hqG, hGH, hr, hrG, hrH⟩ := localized_spatial_jet_univ (P := fun _ _ => True)
    (isOpen_Ioo.prod hO) hq hQG (fun j i _ => hQH j i) hqVelocity (fun j i _ => hQGVelocity j i)
    hb hbCompact hbSub
  have hrH (j i : Fin d) : MemLp (rH j i) 2 volume := hrH j i trivial
  have hrLoc := hr.locallyIntegrable (by norm_num)
  have hgLoc (j : Fin d) := (hrG j).locallyIntegrable (by norm_num)
  have hhLoc (j i : Fin d) := (hrH j i).locallyIntegrable (by norm_num)
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  have hAij (i j : Fin d) : MemLp (fun z => A z i j) ∞
      ((volume : Measure (TimeVelocity d)).restrict S) :=
    (coefficient_entry_memLp_top A hAmeas hlam hAlower hAupper hS i j).2.2
  obtain ⟨hcG, hcD, hcE, -⟩ := energy_weights_memLp_top S η hη hηcompact ζ hζ hζcompact
  have hcR := supportIndicator_memLp_top S η hζ.continuous hζcompact
  let mG (ε : ℝ) (k : Fin d) := SpacetimeMollifier.spacetimeMollification ε (rG k)
  let mH (ε : ℝ) (j i : Fin d) := SpacetimeMollifier.spacetimeMollification ε (rH j i)
  let P (g : Fin d → TimeVelocity d → ℝ) (h : Fin d → Fin d → TimeVelocity d → ℝ) :=
    ∫ z in S, ζ z.1 * (∑ i, ∑ j, A z i j * h j i z) *
      localizedGradientDivergence η (fun z j => g j z) (fun z j i => h j i z) z ∂volume
  let E (h : Fin d → Fin d → TimeVelocity d → ℝ) :=
    ∫ z in S, ζ z.1 * η z.2 ^ 2 * ∑ k, ∑ i, h k i z ^ 2 ∂volume
  let G (g : Fin d → TimeVelocity d → ℝ) :=
    ∫ z in S, ζ z.1 * (tsupport η).indicator (fun y => ∑ k, g k (z.1, y) ^ 2) z.2 ∂volume
  have hg k := (SpacetimeMollifierL2.spacetimeMollification_strongL2 (hrG k)).restrict S
  have hh j i := (SpacetimeMollifierL2.spacetimeMollification_strongL2 (hrH j i)).restrict S
  have hAconv := Analysis.StrongL2Limit.finset_sum Finset.univ fun i _ =>
    Analysis.StrongL2Limit.finset_sum Finset.univ fun j _ => (hh j i).weight (hAij i j)
  have hDconv := Analysis.StrongL2Limit.finset_sum Finset.univ fun k _ =>
    ((hg k).weight (hcG k)).add ((hh k k).weight hcD)
  have expand_divergence (g : Fin d → TimeVelocity d → ℝ)
      (h : Fin d → Fin d → TimeVelocity d → ℝ) (z : TimeVelocity d) :
      ζ z.1 * localizedGradientDivergence η (fun z j => g j z) (fun z j i => h j i z) z =
        ∑ k : Fin d, ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2) * g k z +
          (-1 : ℝ) * ζ z.1 * η z.2 ^ 2 * h k k z) := by
    unfold localizedGradientDivergence
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hP : Filter.Tendsto (fun ε => P (mG ε) (mH ε)) (𝓝[>] 0) (𝓝 (P rG rH)) := by
    have swap (z : TimeVelocity d) (s t : ℝ) : ζ z.1 * s * t = s * (ζ z.1 * t) := by ring
    simpa only [P, mG, mH, swap, expand_divergence] using hAconv.pairing hDconv
  have hE : Filter.Tendsto (fun ε => E (mH ε)) (𝓝[>] 0) (𝓝 (E rH)) := by
    simpa only [E, mH, Fintype.sum_prod_type] using
      Analysis.StrongL2Limit.weighted_sum_sq (κ := Fin d × Fin d) (fun ij => hh ij.1 ij.2) hcE
  have hG : Filter.Tendsto (fun ε => G (mG ε)) (𝓝[>] 0) (𝓝 (G rG)) := by
    have expand_indicator (g : Fin d → TimeVelocity d → ℝ) (z : TimeVelocity d) :
        ζ z.1 * (tsupport η).indicator (fun y => ∑ k, g k (z.1, y) ^ 2) z.2 =
          (ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2) * ∑ k, g k z ^ 2 := by
      by_cases hz : z.2 ∈ tsupport η <;> simp [hz]
    simpa only [G, mG, expand_indicator] using Analysis.StrongL2Limit.weighted_sum_sq hg hcR
  have hsmooth : ∀ᶠ ε in 𝓝[>] 0,
      lam / 2 * E (mH ε) - principalCoercivityConstant d lam Lam M K * G (mG ε) ≤
        -P (mG ε) (mH ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hqε := SpacetimeMollifier.contDiff_spacetimeMollification hε (localizedScalar b q) hrLoc
    have hGεLp j := SpacetimeMollifierL2.spacetimeMollification_memLp hε _ (hrG j)
    have hHεLp j i := SpacetimeMollifierL2.spacetimeMollification_memLp hε _ (hrH j i)
    have hGεid z j := congrFun (SpacetimeMollifier.velocityGradient_spacetimeMollification hε j
      _ _ hrLoc (hgLoc j) (hqG j)) z
    have hHεid z j i := congrFun (SpacetimeMollifier.velocityHessian_spacetimeMollification hε
      hrLoc (hgLoc j) (hhLoc j i) (hqG j) (hGH j i trivial)) z
    have hs := smooth_principal_coercivity_spacetime lam Lam M K s₀ s₁ O hO A
      (mollifiedLocalizedScalar ε b q)
      (fun z j => SpacetimeMollifier.spacetimeMollification ε (rG j) z)
      (fun z j i => SpacetimeMollifier.spacetimeMollification ε (rH j i) z)
      hAmeas hlam hlamLam hA hAlower hAupper hAderiv hqε hGεid hHεid
      (fun j => (hGεLp j).restrict S) (fun j i => (hHεLp j i).restrict S)
      η hη hηcompact hηsupport hηnonneg hηle hηderiv ζ hζ hζcompact hζnonneg
    exact hs
  exact le_of_tendsto_of_tendsto ((hE.const_mul (lam / 2)).sub
    (hG.const_mul (principalCoercivityConstant d lam Lam M K))) hP.neg hsmooth

end

end HypoellipticAleksandrov.Parabolic
