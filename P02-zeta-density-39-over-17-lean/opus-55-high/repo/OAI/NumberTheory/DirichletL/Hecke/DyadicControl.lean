module
public import OAI.NumberTheory.DirichletL.Hecke.LogarithmicActual
public import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
public import OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem original_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  pm_3111
  pm_3109
  pm_6702
  rw [hregular] at hbound
  pm_3110
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : LFunction χ z = LFunction ψ z*factors χ.modulus ψ z :=
    LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      (LFunction ψ z)⁻¹*(factors χ.modulus ψ z)⁻¹ := by
    rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos]
    simp only [HeckeReciprocal.reciprocal, ite_eq_right hψ]
  pm_3108
  calc
    _ ≤ (‖LFunction ψ z‖+‖(LFunction ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (LFunction ψ z))
      have h2 := mul_le_mul_of_nonneg_left hdel2 (norm_nonneg ((LFunction ψ z)⁻¹))
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_original_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖ ≤
          C*(presentationComplexity (χ j) t)^ε := by
  pm_3547 C hC hbound original_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  pm_3112

end SevenEighths.HeckeDyadicControl

end

end OAI
