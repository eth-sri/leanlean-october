module
public import OAI.NumberTheory.DirichletL.Hecke.Reciprocal
public import OAI.NumberTheory.DirichletL.Hecke.IdealOperations
public import OAI.NumberTheory.DirichletL.EulerFactors
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

section
variable (M : Ideal O) (ψ : Character)
include M ψ
theorem factors_eq (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  positivity

theorem factors_ne_zero {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    aesop
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val
end

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by aesop)).differentiableWithinAt

section
variable (χ ψ : Character) (hmask : ∀ I : Ideal O, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff ψ I else 0) {s : ℂ} (hs : 0 < s.re)
include χ ψ hmask s hs
theorem regularizedL_eq_of_mask :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  pm_3125
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  pm_7799
  pm_3116 h0 z hz'
  pm_3117 h1 z hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem LFunction_eq_of_mask (h1 : s ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  pm_3256 h0 s h hs
  have h := regularizedL_eq_of_mask χ ψ hmask hs
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1, mul_assoc] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) h
end

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

section
variable (χ ψ : Character) (hmask : ∀ I : Ideal O, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
include χ ψ hmask
theorem principal_iff_of_mask :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

theorem LFunction_eq_of_mask_nonprincipal
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  pm_5667
  have ha (η : Character) (hη : η.residue ≠ 1) :
      AnalyticOnNhd ℂ (LFunction η) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (LFunction_differentiableAt η (by intro h; simp [h] at hz)
      (Or.inr hη)).differentiableWithinAt
  pm_3125
  apply Continuation.product_identity_on_halfPlane 0 1
    (LFunction ψ) (factors χ.modulus ψ) (LFunction χ) (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem LFunction_eq_of_mask_nonpole
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rcases hpole with h1 | hχ
  · exact LFunction_eq_of_mask χ ψ hmask hs h1
  · exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs
end

theorem exists_primitive_zero (χ : Character) {s : ℂ}
    (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) ∧ LFunction ψ s = 0 := by
  obtain ⟨ψ, _, hp, _, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, ?_, ?_⟩
  · rcases hpole with h1 | hχ
    · exact Or.inl h1
    · exact Or.inr (fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h))
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero] at hz
    exact hz.resolve_right (factors_ne_zero χ.modulus ψ hs)

end SevenEighths.HeckeFiniteDeletion

end

end OAI
