module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
import all HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives

open private HypoellipticAleksandrov.Parabolic.spatialShift_measurableEmbedding from HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
open private HypoellipticAleksandrov.Parabolic.spatialShift_comp_neg_apply from HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
open private HypoellipticAleksandrov.Parabolic.spatialShift_neg_comp_apply from HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives


/-!
# Spacetime spatial difference-quotient transposition

This file establishes the fixed-step, coefficient-free transposition identity
for a spatial difference quotient against a compactly supported spacetime test.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}












/-- A forward spatial difference quotient transposes to the negative backward
quotient on any raw carrier containing the test support and its forward shift. -/
theorem setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
     (U : HypoellipticAleksandrov.Parabolic.Region d)
    (k : Fin d) (h : ℝ) (u φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hu : ParabolicMemLpOn U (2 ) u)
    (hφ : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U)
    (hφshift : Set.MapsTo (spatialShift k h) (tsupport φ) U) :
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z) =
      -∫ z in U,
        u z * spatialDifferenceQuotient k (-h) φ z := by
  let sharedTerm_2b05597970 := (∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z ∂volume)
  let sharedTerm_aa8859ac1b := (∫ z, u z * spatialDifferenceQuotient k (-h) φ z ∂volume)
  rcases eq_or_ne h 0 with rfl | hh
  · simp [spatialDifferenceQuotient]
  let ψ  := spatialTranslate k (-h) φ
  let A  := fun z => spatialTranslate k h u z * φ z
  let B  := fun z => u z * φ z
  let C  := fun z => u z * ψ z
  have hψcont : Continuous ψ := by
    change Continuous (φ ∘ spatialShift k (-h))
    exact hφ.comp <| (id (Homeomorph.continuous (Homeomorph.addRight (0, -h • PDE.basisVec k))))
  have hψcompact : HasCompactSupport ψ := by
    exact HasCompactSupport.spatialTranslate hφcompact
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    rw [mem_tsupport_spatialTranslate_iff] at hz
    have hforward := hφshift hz
    simpa only [ψ, _root_.HypoellipticAleksandrov.Parabolic.spatialShift_comp_neg_apply] using hforward


  have hqU : tsupport (spatialDifferenceQuotient k (-h) φ) ⊆ U := by
    apply tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) φ (fun _ hz => hz) hφU
    simpa using hφshift
  have hφmem : MemLp φ (2 ) (volume.restrict U) :=
    hφ.memLp_of_hasCompactSupport hφcompact
  have hψmem : MemLp ψ (2 ) (volume.restrict U) :=
    hψcont.memLp_of_hasCompactSupport hψcompact
  have hBOn  := hu.integrable_mul hφmem
  have hCOn  := hu.integrable_mul hψmem
  have hBsupport : Function.support B ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    apply hz
    simp [B, hzero]
  have hCsupport : Function.support C ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hψU hzs)
    apply hz
    simp [C, hzero]
  have hB  :=
    (integrableOn_iff_integrable_of_support_subset hBsupport).mp hBOn
  have hC  :=
    (integrableOn_iff_integrable_of_support_subset hCsupport).mp hCOn
  let hμ := spatialShift_measurePreserving k h
  let hembed := _root_.HypoellipticAleksandrov.Parabolic.spatialShift_measurableEmbedding k h
  have hA : Integrable A  := by
    have hcomp  :=
      (hμ.integrable_comp_emb hembed).mpr hC
    convert hcomp using 1
    ext z
    dsimp [A, C, ψ, Function.comp_def]
    rw [_root_.HypoellipticAleksandrov.Parabolic.spatialShift_neg_comp_apply]
  have hAint : (∫ z, A z) = ∫ z, C z := by
    have hcomp := hμ.integral_comp hembed C
    calc
      (∫ z, A z) = ∫ z, C (spatialShift k h z) := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp [A, C, ψ]
        rw [_root_.HypoellipticAleksandrov.Parabolic.spatialShift_neg_comp_apply]
      _ = ∫ z, C z := hcomp
  have hDsupport : Function.support (fun z => spatialDifferenceQuotient k h u z * φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    exact hz (by rw [hzero, mul_zero])
  have hRsupport : Function.support
      (fun z => u z * spatialDifferenceQuotient k (-h) φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero  :=
      image_eq_zero_of_notMem_tsupport fun hzs => hnot (hqU hzs)
    exact hz (by rw [hzero, mul_zero])
  calc
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z) =
        ∫ z, spatialDifferenceQuotient k h u z * φ z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      by_contra hne
      exact hz (hDsupport (Function.mem_support.mpr hne))
    _ = ∫ z, (A z - B z) / h := by
      congr with z
      dsimp [A, B]
      ring
    _ = ((∫ z, A z) - ∫ z, B z) / h := by
      rw [integral_div, integral_sub hA hB]
    _ = ((∫ z, C z) - ∫ z, B z) / h := by rw [hAint]
    _ = ∫ z, (C z - B z) / h := by
      rw [← integral_sub hC hB, ← integral_div]
    _ = -sharedTerm_aa8859ac1b := by
      rw [← integral_neg]
      congr with z
      dsimp [B, C, ψ]
      field_simp [hh]
    _ = -sharedTerm_2b05597970 := by
      have hset : (sharedTerm_2b05597970) =
          sharedTerm_aa8859ac1b := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        by_contra hne
        exact hz (hRsupport (Function.mem_support.mpr hne))
      rw [hset]

end HypoellipticAleksandrov.Parabolic
