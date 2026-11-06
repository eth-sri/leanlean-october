module
public import OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins
public import OAI.NumberTheory.DirichletL.Hecke.DyadicControl
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical Topology
open Metric
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

lemma poleRemoved_eq_regularizedL (χ : Character) {s : ℂ} (hs : 0< s.re) :
    HeckeOrigin.poleRemoved χ s=HeckeReciprocal.regularizedL χ s := by
  by_cases h1 : s=1
  · subst s;exact HeckeOrigin.poleRemoved_one χ
  · have h0 : s≠0 := by intro h;simp_all
    rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeReciprocal.regularizedL_eq χ h0 h1]

lemma regular_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0< s.re) : regular χ s=regular ψ s*factors χ.modulus ψ s := by
  by_cases hχ : χ.residue=1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [regular,ite_eq_left hχ,ite_eq_left hψ,HeckePrincipalStrip.sourceNormalized,
      poleRemoved_eq_regularizedL χ hs,poleRemoved_eq_regularizedL ψ hs]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue≠1 := fun h=>hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    rw [regular_eq_nonprincipal χ hχ,regular_eq_nonprincipal ψ hψ]
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

section
variable (χ : Character)
include χ
lemma regular_eq_detector (s : ℂ) :
    regular χ s=if χ.residue=1 then detectorEntire χ s/(s+1) else detectorEntire χ s := by
  by_cases hχ : χ.residue=1
  · simp [regular,detectorEntire,HeckePrincipalStrip.sourceNormalized,hχ]
  · simp [regular,detectorEntire_eq_nonprincipal χ hχ,hχ]

lemma regular_nonzero_of_detector {s : ℂ} (hs : 0< s.re)
    (hz : detectorEntire χ s≠0) : regular χ s≠0 := by
  rw [regular_eq_detector]
  split_ifs
  · apply div_ne_zero hz
    pm_6105 h Complex.add_re Complex.one_re Complex.zero_re
  grind

lemma reciprocal_norm_le_regular_inverse_on_positive {s : ℂ}
    (hs : 0< s.re) (hz : regular χ s≠0) :
    ‖HeckeReciprocal.reciprocal χ s‖≤‖(regular χ s)⁻¹‖ := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · by_cases h1 : s=1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one χ hχ,norm_zero]
      exact norm_nonneg _
    have hp : s+1≠0 := by
      pm_6105 h Complex.add_re Complex.one_re Complex.zero_re
    have hL : LFunction χ s≠0 := by
      intro h
      apply hz
      simp [regular,hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1,h]
    have heq : HeckeReciprocal.reciprocal χ s=((s-1)/(s+1))*(regular χ s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
      simp only [regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1]
      field_simp
    pm_1219 heq
    pm_7412 hs.le
  · simp only [HeckeReciprocal.reciprocal,regular,ite_eq_right hχ,le_refl]
end

section
variable (e ε : ℝ) (he : 0<e) (he' : e<1/1000) (hε : 0<ε)
include e ε he he' hε
theorem original_regular_disk_control :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  pm_3111
  intro χ a t ha ha' hzero z hz
  pm_554 hn
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [regular_eq_of_mask χ ψ hmask hwp, hh, zero_mul]
  pm_6702
  pm_3110
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : regular χ z = regular ψ z*factors χ.modulus ψ z :=
    regular_eq_of_mask χ ψ hmask hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      HeckeReciprocal.reciprocal ψ z*(factors χ.modulus ψ z)⁻¹ :=
    HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos
  have hrec := reciprocal_norm_le_regular_inverse_on_positive ψ hzpos (hzeroψ z hz2)
  pm_3108
  calc
    _ ≤ (‖regular ψ z‖+‖(regular ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (regular ψ z))
      have h2 := mul_le_mul hrec hdel2 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_regular_control :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→ Character)
      (T a : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j t,|t|≤(3*i+2:ℕ)*T →
      ∀z∈closedBall ((2:ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
          C*(presentationComplexity (χ j) t)^ε := by
  pm_3547 C hC hbound original_regular_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a i hT ha ha1 hmax j t ht z hz
  apply hbound (χ j) a t (by linarith) ha1 _ z hz
  intro w hw
  have hre : 0<w.re := by have h:=LogarithmicControl.disk_re_gt hw;linarith
  exact regular_nonzero_of_detector (χ j) hre
    (detectorEntire_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht (ball_subset_closedBall hw))

theorem buffered_rectangle_reciprocal_bound :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→ Character)
      (T a H : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      H≤(3*i+2:ℕ)*T → detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j z,a+16*e≤z.re → z.re≤2 → |z.im|≤H →
        ‖HeckeReciprocal.reciprocal (χ j) z‖≤C*(presentationComplexity (χ j) H)^ε := by
  pm_3547 C hC hbound buffered_regular_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a H i hT ha ha1 hHT hmax j z hzl hzr hzi
  have hz : z∈closedBall ((2:ℂ)+z.im*Complex.I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hb := hbound χ T a i hT ha ha1 hmax j z.im (hzi.trans hHT) z hz
  have hc : presentationComplexity (χ j) z.im≤presentationComplexity (χ j) H := by
    unfold presentationComplexity complexity
    have hH : 0≤H := (abs_nonneg _).trans hzi
    rw [abs_of_nonneg hH]
    gcongr
  have hnonneg : 0≤presentationComplexity (χ j) z.im := by
    unfold presentationComplexity complexity
    positivity
  apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnonneg hc hε.le) hC.le
end

end SevenEighths.ProbeHighRowFamily


end OAI
