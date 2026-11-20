module

public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientSafeCarrierBridge
public import HypoellipticAleksandrov.Parabolic.IntermediateSpatialCutoffCollar
public import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialSliceDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpatialDifferenceQuotientL2Bound
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import HypoellipticAleksandrov.Parabolic.CrossVelocityWeakDerivativeCommutation
import HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy

import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry

import HypoellipticAleksandrov.Analysis.L2Convergence
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm
import HypoellipticAleksandrov.Parabolic.WeakJetLocalization

/-!
# Fixed-direction generic spatial difference-quotient estimate

This module supplies the non-circular fixed-direction Caccioppoli estimate used by
the generic pre-lift spatial difference-quotient estimate.  The private
infrastructure below records the signed collar geometry, product-cutoff
calculus, locally square-integrable fluxes, and coefficient quotient bounds.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set Analysis
open scoped Convex ENNReal MatrixOrder

section
variable {d : ℕ} {I : Set ℝ} {O₀ O₂ : Set (PDE.Vec d)} {δ h : ℝ}
  (hcarrier : Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀) (hh : |h| ≤ δ)
  (k : Fin d)
include δ hcarrier hh

/-- A spatial coordinate-shift collar contains every full signed spacetime
segment starting in its intermediate cylinder. -/
private theorem segment_spatialShift_subset_prod_of_carrier :
    ∀ z ∈ I ×ˢ O₂, [z -[ℝ] spatialShift k h z] ⊆ I ×ˢ O₀ := by
  intro z hz
  exact (Dirichlet.segment_spatialShift_subset_prod_spatialCoordinateShiftCarrier
    k z hh (show z ∈ I ×ˢ closure O₂ from ⟨hz.1, subset_closure hz.2⟩)).trans
    (Set.prod_mono Subset.rfl hcarrier)

/-- The signed collar also supplies the endpoint translation required by the
quotient-test energy identity. -/
private theorem mapsTo_spatialShift_prod_of_carrier :
    MapsTo (spatialShift k h) (I ×ˢ O₂) (I ×ˢ O₀) := 
  fun z hz => segment_spatialShift_subset_prod_of_carrier hcarrier hh k z hz
    (right_mem_segment ℝ _ _)

end

section
variable {d : ℕ}

/-- The spatial projection of the signed collar contains the coordinate
segment needed by the fixed-time mean-value estimate. -/
private theorem segment_add_smul_basisVec_subset_of_carrier {O₀ O₂ : Set (PDE.Vec d)} {δ h : ℝ}
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ) (k : Fin d) :
    ∀ y ∈ O₂, [y -[ℝ] y + h • PDE.basisVec k] ⊆ O₀ := by
  intro y hy w hw
  let π := (LinearMap.snd ℝ ℝ (PDE.Vec d)).toAffineMap
  change w ∈ [π (0, y) -[ℝ] π (spatialShift k h (0, y))] at hw
  rw [← _root_.image_segment] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact (segment_spatialShift_subset_prod_of_carrier hcarrier hh k (0, y)
    (show (0, y) ∈ (Set.univ : Set ℝ) ×ˢ O₂ from ⟨trivial, hy⟩) hz).2

/-- On the inner product cylinder the two plateau factors make the product
cutoff exactly one. -/
private theorem productCutoff_eq_one_on_inner {t₁ t₂ : ℝ} {O₁ : Set (PDE.Vec d)}
    (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ∀ t ∈ Icc t₁ t₂, zeta t = 1)
    (heta : ∀ y ∈ closure O₁, eta y = 1) :
    ∀ z ∈ Ioo t₁ t₂ ×ˢ O₁,
      zeta z.1 * eta z.2 ^ 2 = 1 := by
  intro z hz
  rw [hzeta z.1 ⟨hz.1.1.le, hz.1.2.le⟩, heta z.2 (subset_closure hz.2)]
  norm_num

/-- Bounds for the separated product cutoff used in the fixed-step energy argument. -/
private theorem productCutoff_data {s₀ t₁ t₂ s₁ Keta Kzeta : ℝ} {O₁ O₂ : Set (PDE.Vec d)}
    (eta : PDE.QuantitativeSmoothCutoff (closure O₁) O₂ Keta) (zeta : ℝ → ℝ)
    (hzetaSmooth : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta)
    (hzetaNonneg : ∀ t, 0 ≤ zeta t) (hzetaLe : ∀ t, zeta t ≤ 1)
    (hzetaOne : ∀ t ∈ Icc t₁ t₂, zeta t = 1) (hzetaSupport : tsupport zeta ⊆ Ioo s₀ s₁)
    (hzetaDeriv : ∀ t, |_root_.deriv zeta t| ≤ Kzeta) :
    let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
    ContDiff ℝ (⊤ : ℕ∞) w ∧ HasCompactSupport w ∧ tsupport w ⊆ Ioo s₀ s₁ ×ˢ O₂ ∧
    (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧ (∀ z, |timeDerivative w z| ≤ Kzeta) ∧
    (∀ i z, velocityGradient w z i ^ 2 ≤ 4 * Keta ^ 2 * w z) ∧
    (∀ z ∈ Ioo t₁ t₂ ×ˢ O₁, w z = 1) := by
  let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
  have hηsq (y : PDE.Vec d) : eta y ^ 2 ≤ 1 := by
    nlinarith [eta.nonneg y, eta.le_one y]
  have hw (z : TimeVelocity d) : 0 ≤ w z ∧ w z ≤ 1 := by
    refine ⟨mul_nonneg (hzetaNonneg z.1) (sq_nonneg _), ?_⟩
    exact (mul_le_mul (hzetaLe z.1) (hηsq z.2) (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hD (i : Fin d) (y : PDE.Vec d) : |spatialPartial i eta y| ≤ Keta := by
    simpa only [spatialPartial, PDE.classicalGradient_apply] using eta.abs_classicalGradient_apply_le y i
  refine ⟨WeakGradientTimeEnergy.fderiv_timeVelocityCutoff zeta eta hzetaSmooth eta.smooth,
    WeakGradientTimeEnergy.timeVelocityCutoff_hasCompactSupport zeta eta hzetaCompact eta.hasCompactSupport,
    (WeakGradientTimeEnergy.tsupport_timeVelocityCutoff zeta eta).le.trans
      (prod_mono hzetaSupport eta.tsupport_subset), hw, ?_, ?_,
    productCutoff_eq_one_on_inner zeta eta hzetaOne eta.eq_one_on_inner⟩
  · intro z
    unfold timeDerivative
    rw [WeakGradientTimeEnergy.fderiv_timeVelocityCutoff_time eta eta.smooth zeta hzetaSmooth,
      abs_mul, abs_pow, abs_of_nonneg (eta.nonneg _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hηsq _)).trans (hzetaDeriv _)
  · intro i z
    unfold velocityGradient
    rw [WeakGradientTimeEnergy.fderiv_timeVelocityCutoff_spatial eta eta.smooth zeta hzetaSmooth]
    have hDs : (spatialPartial i eta z.2) ^ 2 ≤ Keta ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hD i z.2))).2 (hD i z.2)
    have hz₀ := hzetaNonneg z.1
    have hzSq : zeta z.1 ^ 2 ≤ zeta z.1 := by nlinarith [hzetaLe z.1]
    change _ ≤ 4 * Keta ^ 2 * (zeta z.1 * eta z.2 ^ 2)
    calc
      _ = 4 * zeta z.1 ^ 2 * eta z.2 ^ 2 * spatialPartial i eta z.2 ^ 2 := by ring
      _ ≤ 4 * zeta z.1 * eta z.2 ^ 2 * Keta ^ 2 := by gcongr
      _ = _ := by ring

/-- Two-sided Loewner control makes each local coefficient flux entry square
integrable on compact subsets of the outer cylinder. -/
private theorem fluxEntry_parabolicMemLpOn_compact {U K : Set (TimeVelocity d)} {lam Lam : ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : TimeVelocity d → PDE.Mat d)
    (hEll : ∀ z ∈ U,
      lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d ↦ A z i j) U)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, ParabolicMemLpOn U 2 (G j))
    (i j : Fin d) :
    ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z) := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  have haMeas : AEStronglyMeasurable (fun z : TimeVelocity d ↦ A z i j)
      (timeVelocityVolumeOn K) :=
    (hA i j).continuousOn.mono hKU |>.aestronglyMeasurable hKmeas
  have hGK : ParabolicMemLpOn K 2 (G j) := (hG j).mono hKU
  have haBound : ∀ᵐ z ∂timeVelocityVolumeOn K, |A z i j| ≤ Lam := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact abs_apply_le_of_loewner hlam (hEll z (hKU hz)).1
      (hEll z (hKU hz)).2 i j
  exact (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
    (hlam.le.trans hlamLam) haMeas hGK haBound).1

/-- Joint `C¹` coefficient regularity and the signed collar convert the
displayed spatial derivative bound into a uniform coefficient quotient bound. -/
private theorem coefficient_spatialDifferenceQuotient_bound {s₀ s₁ : ℝ} {O₀ O₂ : Set (PDE.Vec d)} {δ h Ma : ℝ}
    (hO₀ : IsOpen O₀)
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ)
    (A : TimeVelocity d → PDE.Mat d)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d ↦ A z i j)
      (Ioo s₀ s₁ ×ˢ O₀))
    (hbound : ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₀ →
      |spatialPartial k (fun y : PDE.Vec d ↦ A (z.1, y) i j) z.2| ≤ Ma) :
    ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₂ →
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma := by
  intro i j k z hz
  exact abs_spatialDifferenceQuotient_le_of_spatialSliceFDeriv_bound
    (f := fun x ↦ A x i j) (δ := δ)
    (fun ell g y hg hy ↦
      segment_add_smul_basisVec_subset_of_carrier hcarrier hg ell y hy)
    (fun r hr y hy ↦ by
      have hjoint :=
        ((hA i j (r, y) ⟨hr, hy⟩).differentiableWithinAt (by norm_num)).differentiableAt
          ((isOpen_Ioo.prod hO₀).mem_nhds ⟨hr, hy⟩)
      exact hjoint.comp y
        ((differentiableAt_const (c := r)).prodMk differentiableAt_id))
    (fun r hr ell y hy ↦ hbound i j ell (r, y) ⟨hr, hy⟩)
    k h z hh hz

/-- Exact forward product expansion of one row of the principal flux. -/
private theorem spatialDifferenceQuotient_principalFluxRow (A : TimeVelocity d → PDE.Mat d)
    (G : Fin d → TimeVelocity d → ℝ) (i k : Fin d) (h : ℝ) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j : Fin d, A x i j * G j x) =
      fun z ↦ ∑ j : Fin d, (
        spatialTranslate k h (fun x ↦ A x i j) z *
            spatialDifferenceQuotient k h (G j) z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z) := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An undifferenced source pairs with the backward quotient at the cost of a
single global weak spatial derivative, with no inverse-step factor. -/
private theorem abs_setIntegral_mul_backwardQuotient_le {S : Set (TimeVelocity d)} {k : Fin d} {h : ℝ} (hh : h ≠ 0)
    {R ψ Dψ : TimeVelocity d → ℝ} (hR : ParabolicMemLpOn S 2 R)
    (hψ : MemLp ψ 2 volume) (hDψ : MemLp Dψ 2 volume)
    (hweak : HasWeakVelocityPartialDerivOn univ k ψ Dψ) :
    |∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z| ≤
      (eLpNorm R 2 (timeVelocityVolumeOn S)).toReal * (eLpNorm Dψ 2 volume).toReal := by
  obtain ⟨hback, hn⟩ := hweak.exists_spatialDifferenceQuotient_memLp_norm_le
    univ isOpen_univ univ k (-h) (neg_ne_zero.mpr hh) ψ Dψ (hψ.restrict _) (hDψ.restrict _)
    (fun _ _ => subset_univ _)
  rw [Lp.norm_toLp, Lp.norm_toLp, timeVelocityVolumeOn, Measure.restrict_univ] at hn
  have hback' : MemLp (spatialDifferenceQuotient k (-h) ψ) 2 volume := by
    simpa only [ParabolicMemLpOn, timeVelocityVolumeOn, Measure.restrict_univ] using hback
  rw [← Real.norm_eq_abs]
  refine (norm_integral_mul_le_eLpNorm_two hR (hback'.restrict S)).trans ?_
  exact mul_le_mul_of_nonneg_left ((ENNReal.toReal_mono hback'.eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)).trans hn) ENNReal.toReal_nonneg

end

/-- The square of a localized product derivative is bounded by the sum of
an energy of the differentiated function and a cutoff error. -/
private theorem weighted_product_derivative_sq_le {w q H dw K : ℝ}
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hdw : dw ^ 2 ≤ 4 * K ^ 2 * w) :
    (dw * q + w * H) ^ 2 ≤ 2 * (4 * K ^ 2 * q ^ 2 + w * H ^ 2) := by
  calc
    _ ≤ 2 * ((dw * q) ^ 2 + (w * H) ^ 2) := by nlinarith [sq_nonneg (dw * q - w * H)]
    _ ≤ _ := by
      simp only [mul_pow]
      gcongr
      · exact hdw.trans (mul_le_of_le_one_right (by positivity) hw₁)
      · simpa only [pow_two] using mul_le_of_le_one_right hw hw₁

/-- A divergence-form equation with square-integrable value, gradient and source. -/
structure DivergenceFormL2Data {d : ℕ} (U : Set (TimeVelocity d)) (lam Lam Ma : ℝ)
    (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ) : Prop where
  elliptic : ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)
  smooth : ∀ i j, ContDiffOn ℝ 1 (fun z => A z i j) U
  derivativeBound : ∀ i j k z, z ∈ U → |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ Ma
  memLpValue : ParabolicMemLpOn U 2 q
  memLpGradient : ∀ j, ParabolicMemLpOn U 2 (G j)
  memLpSource : ParabolicMemLpOn U 2 R
  gradient : ∀ j, HasWeakVelocityPartialDerivOn U j q (G j)
  equation : ∀ φ : TimeVelocity d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    -(∫ z in U, q z * timeDerivative φ z) -
      (∑ i, ∑ j, ∫ z in U, A z i j * G j z * velocityGradient φ z i) = ∫ z in U, R z * φ z

/-- Uniform one-direction spatial difference-quotient control for the gradient
in a tested divergence-form equation. -/
theorem exists_fixedDirection_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
    (d : ℕ) (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ < t₂) (ht₂s₁ : t₂ < s₁)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam Ma : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hMa : 0 ≤ Ma) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
        (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ),
        DivergenceFormL2Data (Ioo s₀ s₁ ×ˢ O₀) lam Lam Ma A q G R →
        ∀ k : Fin d, ∀ h : ℝ, 0 < h → h < δ →
          (∀ j, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (spatialDifferenceQuotient k h (G j))) ∧
          (∑ j, squaredL2Seminorm (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))
              (spatialDifferenceQuotient k h (G j))) ≤
            C * (squaredL2Seminorm (timeVelocityVolumeOn (Ioo s₀ s₁ ×ˢ O₀)) q +
              (∑ j, squaredL2Seminorm (timeVelocityVolumeOn (Ioo s₀ s₁ ×ˢ O₀)) (G j)) +
              squaredL2Seminorm (timeVelocityVolumeOn (Ioo s₀ s₁ ×ˢ O₀)) R) := by
  classical
  obtain ⟨O₂, Keta, eta, δ, hO₂, hO₂compact, hO₁O₂, hO₂O₀,
      hKeta, hδ, hcarrier⟩ :=
    exists_intermediateSpatialCutoff_signedCollar O₀ O₁ hO₀ hO₁compact hO₁O₀
  obtain ⟨zeta, Kzeta, hzetaSmooth, hzetaCompact, hKzeta, hzetaNonneg,
      hzetaLe, hzetaOne, hzetaSupport, hzetaDeriv⟩ :=
    exists_smooth_timePlateau_with_deriv_bound s₀ t₁ t₂ s₁
      hs₀t₁ ht₁t₂.le ht₂s₁
  let Gamma : ℝ :=
    8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
      2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
      ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta
  let alpha : ℝ := lam * Keta ^ 2 / 2
  let beta : ℝ := 4 / lam
  let M : ℝ := 2 * Gamma + Kzeta / 2 + alpha
  let C : ℝ := (4 / lam) * (M + beta)
  have hGamma : 0 ≤ Gamma := by dsimp [Gamma]; positivity
  have hM : 0 ≤ M := by dsimp [M, alpha]; positivity
  have hC : 0 ≤ C := by dsimp [C, beta]; positivity
  refine ⟨C, δ, hC, hδ, ?_⟩
  rintro A q G R ⟨hEll, hA, hAbound, hq, hG, hR, hWeak, hEq⟩ k h hh hhd
  let S : Set (TimeVelocity d) := Ioo s₀ s₁ ×ˢ O₀
  let V : Set (TimeVelocity d) := Ioo s₀ s₁ ×ˢ O₂
  let inner : Set (TimeVelocity d) := Ioo t₁ t₂ ×ˢ O₁
  let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
  let Q : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let H : Fin d → TimeVelocity d → ℝ := fun i ↦ spatialDifferenceQuotient k h (G i)
  have hSopen : IsOpen S := isOpen_Ioo.prod hO₀
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₂
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hinnerMeas : MeasurableSet inner := (isOpen_Ioo.prod hO₁).measurableSet
  have hVS : V ⊆ S := prod_mono_right (subset_closure.trans hO₂O₀)
  have hinnerV : inner ⊆ V := by
    rintro z ⟨hztime, hzspace⟩
    exact ⟨⟨hs₀t₁.trans hztime.1, hztime.2.trans ht₂s₁⟩,
      hO₁O₂ (subset_closure hzspace)⟩
  have habsh : |h| ≤ δ := by rw [abs_of_pos hh]; exact hhd.le
  have hseg : ∀ z ∈ V, [z -[ℝ] spatialShift k h z] ⊆ S := by
    exact segment_spatialShift_subset_prod_of_carrier hcarrier habsh k
  have hshiftV : MapsTo (spatialShift k h) V S :=
    mapsTo_spatialShift_prod_of_carrier hcarrier habsh k
  obtain ⟨hQ, hQnorm⟩ := (hWeak k).exists_spatialDifferenceQuotient_memLp_norm_le
    S hSopen V k h hh.ne' q (G k) hq (hG k) hseg
  have hH (i : Fin d) : ParabolicMemLpOn V 2 (H i) := by
    exact (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hshiftV
  have hQweak (i : Fin d) : HasWeakVelocityPartialDerivOn V i Q (H i) := by
    exact (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hshiftV
  obtain ⟨hwSmooth, hwCompact, hwSupportV, hwBounds, hwTimeBound, hwGradSq, hwOne⟩ :=
    productCutoff_data eta zeta hzetaSmooth hzetaCompact hzetaNonneg hzetaLe
      hzetaOne hzetaSupport hzetaDeriv
  let ψ := fun z => w z * Q z
  let Dψ (i : Fin d) := fun z => velocityGradient w z i * Q z + w z * H i z
  have hD_eq (i : Fin d) : localizedGradient w Q (fun z j => H j z) i = Dψ i := by
    funext z
    simp only [localizedGradient, Dψ]
    ring
  obtain ⟨hψ, hDψ, hψWeak, -, hDψSupport⟩ :=
    localized_gradient_jet_univ (q := Q) (b := w) (QG := fun z j => H j z)
      hVopen hQ hH hQweak hwSmooth hwCompact hwSupportV
  simp only [hD_eq] at hDψ hψWeak hDψSupport
  have hwLp : ParabolicMemLpOn V ∞ w :=
    (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact).restrict V
  have hFlux (i j : Fin d) (K : Set (TimeVelocity d))
      (hK : IsCompact K) (hKS : K ⊆ S) :
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z) :=
    fluxEntry_parabolicMemLpOn_compact hK hKS hlam hlamLam A hEll hA G hG i j
  obtain ⟨-, hfluxInt, -, henergy⟩ :=
    integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation d S hSopen
      A q R G hq hR hG hFlux hWeak hEq w hwSmooth hwCompact (hwSupportV.trans hVS)
      k h hh.ne' (hshiftV.mono_left hwSupportV)
  have hrow (i : Fin d) := spatialDifferenceQuotient_principalFluxRow A G i k h
  let flux (i : Fin d) := fun z => (∑ j, (spatialTranslate k h (fun x => A x i j) z * H j z +
    spatialDifferenceQuotient k h (fun x => A x i j) z * G j z)) * Dψ i z
  have hflux (i : Fin d) : IntegrableOn (flux i) S := by
    simpa only [flux, Dψ, Q, H, hrow i] using hfluxInt i
  have hidentity : (-1 / 2 : ℝ) * (∫ z in S, timeDerivative w z * Q z ^ 2) -
      (∑ i, ∫ z in S, flux i z) = -∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z := by
    simpa only [flux, Dψ, Q, H, ψ, hrow] using henergy
  have hEllShift (z : TimeVelocity d) (hz : z ∈ V) := hEll _ (hshiftV hz)
  have hAquot (z : TimeVelocity d) (hz : z ∈ V) (i j : Fin d) :=
    coefficient_spatialDifferenceQuotient_bound hO₀ hcarrier habsh A hA hAbound i j k z hz
  have hcoercive := setIntegral_fixedDirection_fluxPairing_coercive_absorbed_on_safeCarrier
    hSmeas hVmeas hVS A G H w Q k h lam Lam Ma Keta (Nat.zero_lt_of_lt k.isLt) hlam hKeta
    hwLp (fun z _ => (hwBounds z).1) (fun z _ => (hwBounds z).2) hEllShift hAquot
    (fun z _ i => hwGradSq i z) hQ (fun j => (hG j).mono hVS) hH hDψSupport hflux
  let E := ∫ z in V, w z * ∑ i, H i z ^ 2
  let Ek := ∫ z in V, w z * H k z ^ 2
  let q2 := ∫ z in V, Q z ^ 2
  let g2 := ∑ j, ∫ z in V, G j z ^ 2
  let sq (U : Set (TimeVelocity d)) : (TimeVelocity d → ℝ) → ℝ :=
    squaredL2Seminorm (timeVelocityVolumeOn U)
  let G2 := ∑ j, sq S (G j)
  let R2 := sq S R
  have hEInt := integrable_weighted_sum_sq hwLp hH
  have hEkInt : Integrable (fun z => w z * H k z ^ 2) (timeVelocityVolumeOn V) := by
    have h : Integrable (fun z => (w z * H k z) * H k z) (timeVelocityVolumeOn V) :=
      (hwLp.mul' (hH k) : ParabolicMemLpOn V 2 _).integrable_mul (hH k)
    simpa only [mul_assoc, pow_two] using h
  have hEkE : Ek ≤ E := integral_mono hEkInt hEInt fun z =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => sq_nonneg (H i z))
      (Finset.mem_univ k)) (hwBounds z).1
  have hE0 : 0 ≤ E := integral_nonneg fun z =>
    mul_nonneg (hwBounds z).1 (Finset.sum_nonneg fun i _ => sq_nonneg (H i z))
  have hDnorm : sq univ (Dψ k) ≤ 2 * (4 * Keta ^ 2 * q2 + Ek) := by
    change squaredL2Seminorm (volume.restrict univ) (Dψ k) ≤ _
    rw [Measure.restrict_univ, squaredL2Seminorm, ← integral_real_sq_eq_eLpNorm_sq (hDψ k),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := V) (f := fun z => Dψ k z ^ 2)
        (fun z hz => by rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hDψSupport k h)), zero_pow (by decide)])]
    calc
      _ ≤ ∫ z in V, 2 * (4 * Keta ^ 2 * Q z ^ 2 + w z * H k z ^ 2) :=
        integral_mono ((hDψ k).integrable_sq.mono_measure Measure.restrict_le_self)
          (((hQ.integrable_sq.const_mul (4 * Keta ^ 2)).add hEkInt).const_mul 2)
          (fun z => weighted_product_derivative_sq_le (hwBounds z).1 (hwBounds z).2 (hwGradSq k z))
      _ = _ := by rw [integral_const_mul, integral_add (hQ.integrable_sq.const_mul _) hEkInt,
        integral_const_mul]
  have hsource0 := abs_setIntegral_mul_backwardQuotient_le hh.ne' hR hψ (hDψ k) (hψWeak k)
  have hyoung := mul_le_lambda_eighth_sq_add (lam / 2)
    (eLpNorm R 2 (timeVelocityVolumeOn S)).toReal (eLpNorm (Dψ k) 2 volume).toReal (by positivity)
  have hsource : |∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z| ≤
      (lam / 8) * Ek + alpha * q2 + beta * R2 := by
    refine hsource0.trans (hyoung.trans ?_)
    have hd := mul_le_mul_of_nonneg_left hDnorm (show 0 ≤ (lam / 2) / 8 by positivity)
    simp only [sq, timeVelocityVolumeOn, Measure.restrict_univ, squaredL2Seminorm] at hd
    dsimp only [alpha, beta, R2, sq, squaredL2Seminorm]
    have hb : 2 / (lam / 2) = 4 / lam := by ring
    rw [hb]
    nlinarith only [hd]
  have htime : |∫ z in S, timeDerivative w z * Q z ^ 2| ≤ Kzeta * q2 := by
    rw [show (∫ z in S, timeDerivative w z * Q z ^ 2) = ∫ z in V, timeDerivative w z * Q z ^ 2 by
      simpa only [mul_comm] using setIntegral_mul_eq_of_tsupport_subset hSmeas hVS
        (fun z => Q z ^ 2) (timeDerivative w) ((timeDerivative_tsupport w).trans hwSupportV)]
    calc
      _ ≤ ∫ z in V, |timeDerivative w z * Q z ^ 2| := abs_integral_le_integral_abs
      _ ≤ ∫ z in V, Kzeta * Q z ^ 2 := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
        (hQ.integrable_sq.const_mul _) (ae_of_all _ fun z => by
          change |timeDerivative w z * Q z ^ 2| ≤ Kzeta * Q z ^ 2
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Q z))]
          exact mul_le_mul_of_nonneg_right (hwTimeBound z) (sq_nonneg _))
      _ = _ := by rw [integral_const_mul]
  have hq2G : q2 ≤ G2 := by
    rw [show q2 = sq V Q from integral_real_sq_eq_eLpNorm_sq hQ]
    have hQsq : sq V Q ≤ sq S (G k) := by
      simpa only [sq, squaredL2Seminorm, Lp.norm_toLp] using
        pow_le_pow_left₀ (norm_nonneg _) hQnorm 2
    exact hQsq.trans (Finset.single_le_sum (fun i _ => squaredL2Seminorm_nonneg _ _) (Finset.mem_univ k))
  have hg2G : g2 ≤ G2 := Finset.sum_le_sum fun j _ =>
    (integral_real_sq_eq_eLpNorm_sq ((hG j).mono hVS)).le.trans
      (squaredL2Seminorm_mono_measure (hG j) (Measure.restrict_mono_set volume hVS))
  have hbound : (lam / 4) * E ≤ M * G2 + beta * R2 := by
    have ht := (neg_le_abs _).trans htime
    have hs := (le_abs_self _).trans hsource
    have hk := mul_le_mul_of_nonneg_left hEkE (show (0 : ℝ) ≤ lam / 8 by positivity)
    have hq2' := mul_le_mul_of_nonneg_left hq2G (show 0 ≤ Gamma + Kzeta / 2 + alpha by dsimp [alpha]; positivity)
    have hg2' := mul_le_mul_of_nonneg_left hg2G hGamma
    dsimp only [M]
    change (lam / 2) * E ≤ (∑ i, ∫ z in S, flux i z) + Gamma * (q2 + g2) at hcoercive
    nlinarith only [hcoercive, hidentity, ht, hs, hk, hq2', hg2', mul_nonneg hlam.le hE0]
  have hHinner (j : Fin d) := (hH j).mono hinnerV
  refine ⟨hHinner, ?_⟩
  change (∑ j, sq inner (H j)) ≤ C * (sq S q + G2 + R2)
  calc
    _ = ∫ z in inner, ∑ i, H i z ^ 2 := (integral_sum_sq_eq_eLpNorm_sq hHinner).symm
    _ = ∫ z in inner, w z * ∑ i, H i z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hinnerMeas] with z hz
      rw [show w z = 1 from hwOne z hz, one_mul]
    _ ≤ E := integral_mono_measure (Measure.restrict_mono_set volume hinnerV)
      (ae_of_all _ fun z => mul_nonneg (hwBounds z).1 (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hEInt
    _ = (4 / lam) * ((lam / 4) * E) := by field_simp [hlam.ne']
    _ ≤ (4 / lam) * (M * G2 + beta * R2) := by gcongr
    _ ≤ _ := by
      have hG20 : 0 ≤ G2 := Finset.sum_nonneg fun j _ => squaredL2Seminorm_nonneg _ _
      have hR20 : 0 ≤ R2 := squaredL2Seminorm_nonneg _ _
      have hq0 : 0 ≤ sq S q := squaredL2Seminorm_nonneg _ _
      have hb : 0 ≤ beta := by dsimp [beta]; positivity
      dsimp only [C]
      rw [mul_assoc]
      gcongr
      nlinarith only [mul_nonneg hM hq0, mul_nonneg hM hR20, mul_nonneg hb hq0, mul_nonneg hb hG20]

end HypoellipticAleksandrov.Parabolic
