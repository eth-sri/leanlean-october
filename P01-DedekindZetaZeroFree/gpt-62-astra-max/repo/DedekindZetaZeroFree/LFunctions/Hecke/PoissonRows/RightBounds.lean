module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification
public import DedekindZetaZeroFree.Moments.Principal.Contour.ResidueFormulas

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RightHeckeBounds

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

section Helpers

open scoped Classical NumberField Topology
open IsDedekindDomain Filter

private alias fpd_hasSum := DedekindZetaZeroFree.Detector.FiniteEulerDeletion.finite_prime_delete_hasSum

private theorem norm_power (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s = comparisonRealPower q s := by apply @DedekindZetaZeroFree.NormalizedProbe.TripleMellin.TermRace.cpow_positive <;> assumption

private alias L_eq_zeta := DedekindZetaZeroFree.Quantitative.PoissonKernel.Kernel.rf_L_eq_zeta

end Helpers

section Euler

open scoped Classical NumberField

theorem euler_data {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ)
    (ha : ExteriorIdealEuler.IsCoefficient a) (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    (∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I) ≠ 0 ∧
    ‖∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I‖ ≤
      Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)) ∧
    ‖(∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I)⁻¹‖ ≤
      Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)) := by
  have hL := HeckeLogProof.eulerLog_norm_le a ha σ hσ s hs
  rw [← (HeckeLogProof.exp_eulerLog a ha s (lt_of_lt_of_le hσ hs))]
  refine ⟨Complex.exp_ne_zero _, ?_, ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  · rw [← Complex.exp_neg, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    rw [norm_neg]
    exact hL

variable {A : SArithmeticData F} {σ : F →+* ℂ} {η' : RayClassCharacter F A.modulus}
  {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η' hS}

theorem incompleteL_plus_eq (U : CorrectionFactors.Frequency C) (s : ℂ) :
    MaskedHeckeMeromorphic.incompleteL U MaskedHeckeMeromorphic.Row.plus s =
      ∑' I : A.Exterior, ExteriorIdealEuler.summand
        (FrequencyCharacterMasks.plusExteriorCoefficient U) s I := by
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient U MaskedHeckeMeromorphic.Row.plus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient, hn]
  unfold MaskedHeckeMeromorphic.incompleteL
  rw [((tsum_subtype_eq_of_support_subset hsupport).symm)]
  apply tsum_congr
  intro I
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
    I.property.1, I.property.2, ExteriorIdealEuler.summand]

theorem incompleteL_minus_eq (U : CorrectionFactors.Frequency C) (s : ℂ) :
    MaskedHeckeMeromorphic.incompleteL U MaskedHeckeMeromorphic.Row.minus s =
      ∑' I : A.Exterior, ExteriorIdealEuler.summand
        (FrequencyCharacterMasks.minusExteriorCoefficient U) s I := by
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient U MaskedHeckeMeromorphic.Row.minus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
      FrequencyCharacterMasks.minusCoefficient, hn]
  unfold MaskedHeckeMeromorphic.incompleteL
  rw [((tsum_subtype_eq_of_support_subset hsupport).symm)]
  apply tsum_congr
  intro I
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
    FrequencyCharacterMasks.minusCoefficient, FrequencyCharacterMasks.minusExteriorCoefficient,
    I.property.1, I.property.2, ExteriorIdealEuler.summand]

section

variable (u : D.Row) (s : ℂ) (hs : 1 < s.re)

include hs in
theorem Lpsi_eq_tsum :
    D.Lpsi u s = ∑' I : D.recipe.A.Exterior, ExteriorIdealEuler.summand
      (FrequencyCharacterMasks.plusExteriorCoefficient u.toFrequency) s I := by
  rw [D.Lpsi_eq_raw u s hs]
  exact incompleteL_plus_eq u.toFrequency s

include hs in
theorem Llam_eq_tsum :
    D.Llam u s = ∑' I : D.recipe.A.Exterior, ExteriorIdealEuler.summand
      (FrequencyCharacterMasks.minusExteriorCoefficient u.toFrequency) s I := by
  rw [D.Llam_eq_raw u s hs]
  exact incompleteL_minus_eq u.toFrequency s

end

theorem zetaS_eq_tsum (s : ℂ) :
    D.zetaS s = ∑' I : D.recipe.A.Exterior,
      ExteriorIdealEuler.summand (fun _ => (1 : ℂ)) s I := by
  unfold FixedData.zetaS InitialSeparatedEuler.zetaS
  exact tsum_congr (fun I => by simp [ExteriorIdealEuler.summand])

end Euler

alias zetaSCont_eq_zetaS := DedekindZetaZeroFree.Quantitative.PrincipalResidueFormulas.zetaSCont_eq_zetaS

theorem Llam_ne_zero_of_one_lt (u : D.Row) (s : ℂ) (hs : 1 < s.re) : D.Llam u s ≠ 0 := by
  rw [Llam_eq_tsum D u s hs]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).2 s.re hs s le_rfl).1

theorem zetaSCont_ne_zero_of_one_lt (s : ℂ) (hs : 1 < s.re) : D.zetaSCont s ≠ 0 := by
  rw [zetaSCont_eq_zetaS D s hs, zetaS_eq_tsum D s]
  exact (euler_data _ (ExteriorIdealEuler.constant_one_isCoefficient D.recipe.A.cS)
    s.re hs s le_rfl).1

theorem Lpsi_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (s : ℂ), a ≤ s.re → ‖D.Lpsi u s‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a)),
    Real.exp_pos _, fun u s hs => ?_⟩
  rw [Lpsi_eq_tsum D u s (lt_of_lt_of_le ha hs)]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).1 a ha s hs).2.1

theorem Llam_inv_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (s : ℂ), a ≤ s.re → ‖(D.Llam u s)⁻¹‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a)),
    Real.exp_pos _, fun u s hs => ?_⟩
  rw [Llam_eq_tsum D u s (lt_of_lt_of_le ha hs)]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).2 a ha s hs).2.2

theorem zetaSCont_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → ‖D.zetaSCont s‖ ≤ C := by
  obtain ⟨B, hB, h⟩ := PrincipalNumerator.rightHalfPlane_bound D.recipe a ha
  exact ⟨B, hB, fun s hs => h s hs⟩

theorem zetaSCont_inv_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → ‖(D.zetaSCont s)⁻¹‖ ≤ C := by
  obtain ⟨B, hB, h⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound D.recipe a ha
  exact ⟨B, fun s hs => h s hs⟩

alias zetaSCont_analyticOnNhd := DedekindZetaZeroFree.Quantitative.PrincipalResidueFormulas.zetaSCont_analytic

theorem Lpsi_polynomial_growth_principal (u : D.Row) (hu : u.u = 1) (σ0 σ1 : ℝ)
    (h0 : 0 < σ0) (h01 : σ0 ≤ σ1) (h1 : 1 ∉ Set.Icc σ0 σ1) :
    ∃ (C B : ℝ), 0 < C ∧ ∀ (σ : ℝ) (t : ℝ), σ ∈ Set.Icc σ0 σ1 →
      ‖D.Lpsi u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ B := by
  obtain ⟨ρ, hρ, hρb⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ σ ∈ Set.Icc σ0 σ1, ρ ≤ |σ - 1| := by
    by_cases hlt : σ1 < 1
    · refine ⟨1 - σ1, by linarith, fun σ hσ => ?_⟩
      rw [abs_of_neg (by linarith [hσ.2])]
      linarith [hσ.2]
    · have hgt : 1 < σ0 := by
        by_contra hc
        exact h1 ⟨by linarith, by linarith⟩
      refine ⟨σ0 - 1, by linarith, fun σ hσ => ?_⟩
      rw [abs_of_pos (by linarith [hσ.1])]
      linarith [hσ.1]
  obtain ⟨B1, d, hB1, hd, hbd⟩ := PrincipalNumerator.stripNumerator_bound_away_pole D.recipe
    (min σ0 4) 4 ρ (lt_min h0 (by norm_num)) (min_le_right _ _) le_rfl hρ
  obtain ⟨K, hK, hKb⟩ := zetaSCont_norm_le_right D 4 (by norm_num)
  have h2d : 0 < (2 : ℝ) ^ d := by positivity
  refine ⟨B1 * 2 ^ d + K, d, by positivity, ?_⟩
  intro σ t hσ
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hpos : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by rw [hre]; linarith [hσ.1]
  have hne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    apply h1
    have hσ1 : σ = 1 := by
      have := congrArg Complex.re h
      rw [hre] at this
      exact this
    rw [← hσ1]
    exact hσ
  rw [PrincipalResidueFormulas.Lpsi_principal_eq D u hu _ hpos hne]
  have hp : 0 ≤ (1 + |t|) ^ d := Real.rpow_nonneg (by positivity) d
  have hone : (1 : ℝ) ≤ (1 + |t|) ^ d :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) hd
  by_cases h4 : σ ≤ 4
  · have hsep : ρ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
      calc ρ ≤ |σ - 1| := hρb σ hσ
        _ = |(((σ : ℂ) + (t : ℂ) * Complex.I) - 1).re| := by simp
        _ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := Complex.abs_re_le_norm _
    have h : ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        B1 * (2 + |((σ : ℂ) + (t : ℂ) * Complex.I).im|) ^ d :=
      hbd _ (by rw [hre]; exact (min_le_left _ _).trans hσ.1) (by rw [hre]; exact h4) hsep
    rw [him] at h
    have hrp : (2 + |t|) ^ d ≤ 2 ^ d * (1 + |t|) ^ d := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hd
    calc ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B1 * (2 + |t|) ^ d := h
      _ ≤ B1 * (2 ^ d * (1 + |t|) ^ d) := mul_le_mul_of_nonneg_left hrp hB1.le
      _ = B1 * 2 ^ d * (1 + |t|) ^ d := by ring
      _ ≤ (B1 * 2 ^ d + K) * (1 + |t|) ^ d := by nlinarith [mul_nonneg hK.le hp]
  · have h4' : 4 ≤ σ := (not_le.mp h4).le
    have h := hKb ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact h4')
    calc ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K := h
      _ = K * 1 := (mul_one _).symm
      _ ≤ K * (1 + |t|) ^ d := mul_le_mul_of_nonneg_left hone hK.le
      _ ≤ (B1 * 2 ^ d + K) * (1 + |t|) ^ d := by
        nlinarith [mul_nonneg (mul_nonneg hB1.le h2d.le) hp]

end DedekindZetaZeroFree.Quantitative.RightHeckeBounds
