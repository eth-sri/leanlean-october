module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterFiniteOrder
public import DedekindZetaZeroFree.LFunctions.Hecke.CompletionFactor
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedSquareLocalResidues

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter

namespace DedekindZetaZeroFree.LargeSieve




























private lemma inverse_completion_entire (A : ℂ) (hA : A ≠ 0) :
    Differentiable ℂ (fun s : ℂ => A ^ (-(s / 2))) := by
  haveI : NeZero A := ⟨hA⟩
  exact (differentiable_const_cpow_of_neZero A).comp (by fun_prop)

private lemma decompleted_reflection (A : ℂ) (hA : A ≠ 0) (r : ℕ)
    (s z : ℂ) (hg : Complex.Gammaℂ (1 - s) ≠ 0) :
    A ^ (1 / 2 - s) * Complex.Gammaℂ (1 - s) ^ r *
      (Complex.Gammaℂ s)⁻¹ ^ r *
      (z * A ^ (-((1 - s) / 2)) * (Complex.Gammaℂ (1 - s))⁻¹ ^ r) =
    z * A ^ (-(s / 2)) * (Complex.Gammaℂ s)⁻¹ ^ r := by
  have hpow : A ^ (1 / 2 - s) * A ^ (-((1 - s) / 2)) = A ^ (-(s / 2)) := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  have hgam : Complex.Gammaℂ (1 - s) ^ r * (Complex.Gammaℂ (1 - s))⁻¹ ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow]
  calc
    _ = z * (A ^ (1 / 2 - s) * A ^ (-((1 - s) / 2))) *
        (Complex.Gammaℂ (1 - s) ^ r * (Complex.Gammaℂ (1 - s))⁻¹ ^ r) *
        (Complex.Gammaℂ s)⁻¹ ^ r := by ring
    _ = _ := by rw [hpow, hgam]; ring

private lemma gamma_reflected_ne_zero (s : ℂ) (hs : s.re < 0) :
    Complex.Gammaℂ (1 - s) ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  have hpos : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (Complex.Gamma_ne_zero_of_re_pos hpos)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))

private lemma principal_originFactor_analytic {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) :
    AnalyticOnNhd ℂ data.zetaOriginFactor ({1}ᶜ : Set ℂ) := by
  intro s hs
  have hD : (principalDiscriminant F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalDiscriminant_pos F)
  have hp : Differentiable ℂ (fun z : ℂ => (principalDiscriminant F : ℂ) ^ (-z / 2)) := by
    simpa only [neg_div] using inverse_completion_entire _ hD
  have hg : Differentiable ℂ (fun z : ℂ =>
      ((Complex.Gammaℂ (z + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F) :=
    ((Complex.differentiable_Gammaℂ_inv.comp (by fun_prop)).div_const _).pow _
  exact (((hp.mul hg).mul data.E_differentiable).analyticAt s).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

section
variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
include F hF
theorem principalZetaContinuation_analyticOnNhd
      :
    AnalyticOnNhd ℂ (principalZetaContinuation F hF) ({1}ᶜ : Set ℂ) := by
  intro s hs
  exact (analyticAt_id.pow _).mul
    (principal_originFactor_analytic (principalHeckeData F hF) s hs)

theorem principalZetaContinuation_eq
     
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    principalZetaContinuation F hF s =
      (principalHeckeData F hF).E s *
        (principalDiscriminant F : ℂ) ^ (-(s / 2)) *
        (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F / (s * (s - 1)) := by
  rw [principalZetaContinuation_eq_decompleted F hF s hs0 hs1,
    (principalHeckeData F hF).Lambda_eq_div s hs0 hs1]
  rw [show -(s / 2) = -s / 2 by ring]
  ring

theorem principalZetaZeroFactor_analyticAt
      :
    AnalyticAt ℂ (principalHeckeData F hF).zetaOriginFactor 0 := by
  exact principal_originFactor_analytic (principalHeckeData F hF) 0 (by simp)
end


 def principal_residueNumerator {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (s : ℂ) : ℂ :=
  s ^ (principalComplexPlaces F - 1) *
    (principalDiscriminant F : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F * data.E s

private lemma principal_residueNumerator_entire {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) : Differentiable ℂ (principal_residueNumerator data) := by
  have hD : (principalDiscriminant F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalDiscriminant_pos F)
  have hp : Differentiable ℂ (fun z : ℂ => (principalDiscriminant F : ℂ) ^ (-z / 2)) := by
    simpa only [neg_div] using inverse_completion_entire _ hD
  have hg : Differentiable ℂ (fun z : ℂ =>
      ((Complex.Gammaℂ (z + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F) :=
    ((Complex.differentiable_Gammaℂ_inv.comp (by fun_prop)).div_const _).pow _
  exact ((((differentiable_id.pow _).mul hp).mul hg).mul data.E_differentiable)

section
variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
include F hF
private lemma principal_continuation_residueNumerator
      (s : ℂ) :
    principalZetaContinuation F hF s =
      principal_residueNumerator (principalHeckeData F hF) s / (s - 1) := by
  dsimp [principalZetaContinuation, PrincipalHeckeData.zetaOriginFactor, principal_residueNumerator]
  ring

private lemma principal_residueNumerator_one
      :
    principal_residueNumerator (principalHeckeData F hF) 1 =
      principalZetaResidueCoefficient F hF := by
  have hD := principalDiscriminant_pos F
  have hp : (principalDiscriminant F : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.sqrt (principalDiscriminant F) : ℂ))⁻¹ := by
    have h1 : (principalDiscriminant F : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (principalDiscriminant F) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow (le_of_lt hD) (1 / 2), Real.sqrt_eq_rpow]
    rw [Complex.cpow_neg, h1]
  have hg : (Complex.Gammaℂ (1 + 1))⁻¹ / (2 * (Real.pi : ℂ)) =
      (Complex.Gammaℂ 1)⁻¹ := by
    rw [Vendor.inverse_Gammaℂ_recurrence (1 : ℂ)]
    ring
  dsimp [principal_residueNumerator, principalZetaResidueCoefficient, principalPoleCoefficient]
  rw [one_pow, one_mul, neg_div, hp, hg, div_eq_mul_inv, mul_inv, ← inv_pow]
  ring

theorem principalZetaContinuation_local_pole
      :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 1 ∧
      (fun s => principalZetaContinuation F hF s -
        principalZetaResidueCoefficient F hF / (s - 1)) =ᶠ[𝓝[≠] (1 : ℂ)] R := by
  let H := principal_residueNumerator (principalHeckeData F hF)
  have hH : Differentiable ℂ H := principal_residueNumerator_entire _
  have hd : Differentiable ℂ (dslope H 1) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).mpr hH.differentiableOn)
  refine ⟨dslope H 1, hd.analyticAt 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  rw [dslope_of_ne H hs1, slope_def_field,
    principal_continuation_residueNumerator F hF s]
  change H s / (s - 1) - principalZetaResidueCoefficient F hF / (s - 1) =
    (H s - H 1) / (s - 1)
  rw [show H 1 = principalZetaResidueCoefficient F hF from
    principal_residueNumerator_one F hF, sub_div]

theorem principalZetaContinuation_functional_equation
     
    (s : ℂ) (hs : s.re < 0) :
    principalZetaContinuation F hF s =
      (principalDiscriminant F : ℂ) ^ (1 / 2 - s) *
      Complex.Gammaℂ (1 - s) ^ principalComplexPlaces F *
      (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F *
      principalZetaContinuation F hF (1 - s) := by
  have hs0 : s ≠ 0 := by
    intro h; subst s; simp at hs
  have hs1 : s ≠ 1 := by
    intro h; subst s; norm_num at hs
  have ht0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have ht1 : 1 - s ≠ 1 := by
    intro h; apply hs0; linear_combination -h
  rw [principalZetaContinuation_eq_decompleted F hF s hs0 hs1,
    principalZetaContinuation_eq_decompleted F hF (1 - s) ht0 ht1,
    (principalHeckeData F hF).Lambda_functional_equation s hs0 hs1]
  have hD : (principalDiscriminant F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalDiscriminant_pos F)
  have h := decompleted_reflection _ hD (principalComplexPlaces F) s
    ((principalHeckeData F hF).Lambda (1 - s)) (gamma_reflected_ne_zero s hs)
  simp only [← neg_div] at h
  calc
    _ = (principalHeckeData F hF).Lambda (1 - s) *
        (principalDiscriminant F : ℂ) ^ (-s / 2) *
        (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F := by ring
    _ = _ := by rw [← h]; ring
end


end DedekindZetaZeroFree.LargeSieve

end
