module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives

/-!
# Spacetime spatial difference-quotient transposition

This file establishes the fixed-step, coefficient-free transposition identity
for a spatial difference quotient against a compactly supported spacetime test.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} (k : Fin d) (h : ℝ) (z : TimeVelocity d)





/-- A forward spatial difference quotient transposes to the negative backward
quotient on any raw carrier containing the test support and its forward shift. -/
theorem setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
     (U : Set (TimeVelocity d))
    (k : Fin d) (h : ℝ) (u φ : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (hφ : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U)
    (hφshift : Set.MapsTo (spatialShift k h) (tsupport φ) U) :
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z ∂volume) =
      -∫ z in U,
        u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  let ψ : TimeVelocity d → ℝ := spatialTranslate k (-h) φ
  let A : TimeVelocity d → ℝ := fun z => spatialTranslate k h u z * φ z
  let B : TimeVelocity d → ℝ := fun z => u z * φ z
  let C : TimeVelocity d → ℝ := fun z => u z * ψ z
  have hψcont : Continuous ψ := by
    change Continuous (φ ∘ spatialShift k _)
    exact hφ.comp <| by
      change Continuous (fun z : TimeVelocity d => z + (0, (-h) • PDE.basisVec k))
      fun_prop
  have hψcompact : HasCompactSupport ψ := HasCompactSupport.spatialTranslate hφcompact
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    rw [mem_tsupport_spatialTranslate_iff] at hz
    have hforward := hφshift hz
    aesop
  have hqcont : Continuous (spatialDifferenceQuotient k (-h) φ) := by
    change Continuous (fun z => (ψ z - φ z) / (-h))
    fun_prop
  have hqcompact : HasCompactSupport (spatialDifferenceQuotient k (-h) φ) := HasCompactSupport.spatialDifferenceQuotient hφcompact
  have hqU : tsupport (spatialDifferenceQuotient k (-h) φ) ⊆ U := by
    apply tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k _ φ (fun _ hz => hz) hφU
    simp_all
  have hφmem : MemLp φ (2 : ℝ≥0∞) (volume.restrict U) :=
    hφ.memLp_of_hasCompactSupport hφcompact
  have hψmem : MemLp ψ (2 : ℝ≥0∞) (volume.restrict U) :=
    hψcont.memLp_of_hasCompactSupport hψcompact
  have hBOn : IntegrableOn B U volume := hu.integrable_mul hφmem
  have hCOn : IntegrableOn C U volume := hu.integrable_mul hψmem
  have hBsupport : Function.support B ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    grind
  have hCsupport : Function.support C ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hψU hzs)
    grind
  have hB : Integrable B volume :=
    (integrableOn_iff_integrable_of_support_subset hBsupport).mp hBOn
  have hC : Integrable C volume :=
    (integrableOn_iff_integrable_of_support_subset hCsupport).mp hCOn
  let hμ := spatialShift_measurePreserving k h
  let hembed := spatialShift_measurableEmbedding k h
  have hA : Integrable A volume := by
    have hcomp  :=
      (hμ.integrable_comp_emb hembed).mpr hC
    convert hcomp using 1
    aesop
  have hAint : (∫ z, A z ∂volume) = ∫ z, C z ∂volume := by
    have hcomp := hμ.integral_comp hembed C
    calc
      (∫ z, A z ∂volume) = ∫ z, C _ ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        aesop
      _ = ∫ z, C z ∂volume := hcomp
  have hDsupport : Function.support (fun z => spatialDifferenceQuotient k h u z * φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    simp_all
  have hRsupport : Function.support
      (fun z => u z * spatialDifferenceQuotient k (-h) φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  :=
      image_eq_zero_of_notMem_tsupport fun hzs => hnot (hqU hzs)
    simp_all
  calc
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z ∂volume) =
        ∫ z, spatialDifferenceQuotient k h u z * φ z ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      by_contra hne
      exact hz (hDsupport (Function.mem_support.mpr hne))
    _ = ∫ z, (A z - B z) / h ∂volume := by
      congr with z
      dsimp [A]
      ring
    _ = ((∫ z, A z ∂volume) - ∫ z, B z ∂volume) / h := by
      rw [integral_div, integral_sub hA hB]
    _ = ((∫ z, C z ∂volume) - ∫ z, B z ∂volume) / h := by grind
    _ = ∫ z, (C z - B z) / h ∂volume := by
      rw [← integral_sub hC hB, ← integral_div]
    _ = -∫ z, u z * spatialDifferenceQuotient k _ φ z ∂volume := by
      rw [← integral_neg]
      congr with z
      dsimp [B, C, ψ]
      field_simp
    _ = -∫ z in U, u z * spatialDifferenceQuotient k _ φ z ∂volume := by
      have hset : (∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z ∂volume) =
          ∫ z, u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        by_contra hne
        exact hz (hRsupport (Function.mem_support.mpr hne))
      rw [hset]

end HypoellipticAleksandrov.Parabolic
