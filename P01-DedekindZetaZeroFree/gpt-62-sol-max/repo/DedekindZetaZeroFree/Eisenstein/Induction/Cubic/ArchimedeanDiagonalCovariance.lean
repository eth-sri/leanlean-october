module

public import DedekindZetaZeroFree.Eisenstein.Sections.CanonicalFlatFamily
public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.IncomingCasimirEigenfunctions

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators NNReal
open NumberField

namespace DedekindZetaZeroFree.KPContFlatArchDiagonalMultiplier

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def aInfinity (u : InfinitePlace F → ℝ) : KPGlobalTorusFunctionData.E F ζ hζ :=
  KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (fun v => (Real.exp (u v) : ℂ))

theorem aInfinity_mem_center (u : InfinitePlace F → ℝ) :
    aInfinity F ζ hζ u ∈ KPGlobalCenterRationalCharacter.Z F ζ hζ := by
  obtain ⟨c, hc, -⟩ := KPGlobalTorusFiniteStagesCofinality.arch_center F ζ hζ (fun v => (Real.exp (u v) : ℂ))
  have ha : aInfinity F ζ hζ u = (c : KPGlobalTorusFunctionData.E F ζ hζ) := by
    change KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (fun v => (Real.exp (u v) : ℂ)) = (c : KPGlobalTorusFunctionData.E F ζ hζ)
    exact hc.symm
  rw [ha]
  exact c.property

theorem aInfinity_mem_rational (u : InfinitePlace F → ℝ) :
    aInfinity F ζ hζ u ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
  Subgroup.mem_sup_right (aInfinity_mem_center F ζ hζ u)

theorem aInfinity_mem_source (s : ℂ) (u : InfinitePlace F → ℝ) :
    aInfinity F ζ hζ u ∈
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
  aInfinity_mem_rational F ζ hζ u

def sourceElement (s : ℂ) (u : InfinitePlace F → ℝ) :
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
  ⟨aInfinity F ζ hζ u, aInfinity_mem_source F ζ hζ s u⟩

theorem aInfinity_delta (u : InfinitePlace F → ℝ) :
    ((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ) =
      Real.exp (2 * ∑ v, u v) := by
  have hz : (fun v => (Real.exp (u v) : ℂ)) ∈ KPGlobalTorusFunctionData.torusArchDomain F := by
    intro w
    simp only [KPGlobalTorusFunctionData.torusArchDomain, Set.mem_setOf_eq]
    exact_mod_cast (Real.exp_ne_zero (u w))
  have h := KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula
    F ζ hζ (fun v => (Real.exp (u v) : ℂ)) hz
  have h1 : ∀ w : InfinitePlace F,
      ‖((Real.exp (u w) : ℝ) : ℂ)‖ ^ 2 = Real.exp (2 * u w) := by
    intro w
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    norm_num
  calc ((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ)
      = ∏ w : InfinitePlace F, ‖((Real.exp (u w) : ℝ) : ℂ)‖ ^ 2 := h
    _ = ∏ w : InfinitePlace F, Real.exp (2 * u w) := Finset.prod_congr rfl (fun w _ => h1 w)
    _ = Real.exp (∑ w : InfinitePlace F, 2 * u w) :=
        (Real.exp_sum Finset.univ (fun w => 2 * u w)).symm
    _ = Real.exp (2 * ∑ w : InfinitePlace F, u w) := by rw [← Finset.mul_sum]

private theorem nu_arch (u : InfinitePlace F → ℝ) :
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ) =
      Real.exp ((1 / 6 : ℝ) * (2 * ∑ v, u v)) := by
  have hδ := aInfinity_delta F ζ hζ u
  have h6 : ((KPGlobalCenterRationalCharacter.nu F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ)) ^
        (1 / 6 : ℝ) := by
    simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
      KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map, NNReal.rpowMonoidHom_apply,
      NNReal.coe_rpow]
  rw [h6, hδ, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]

theorem source_character (s : ℂ) (u : InfinitePlace F → ℝ) :
    ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character
      (sourceElement F ζ hζ s u) : ℂ) =
        Complex.exp (((1 : ℂ) / 6 + s) * ((2 * ∑ v, u v : ℝ) : ℂ)) := by
  obtain ⟨c, hc, hχc⟩ := KPGlobalTorusFiniteStagesCofinality.arch_center F ζ hζ (fun v => (Real.exp (u v) : ℂ))
  have hcE : c.val = aInfinity F ζ hζ u := hc
  have hR : aInfinity F ζ hζ u ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
    aInfinity_mem_rational F ζ hζ u
  have hsplit : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character
      (sourceElement F ζ hζ s u) : ℂ) =
      ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
        ⟨aInfinity F ζ hζ u, hR⟩ : ℂˣ) : ℂ) *
      ((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (aInfinity F ζ hζ u) : ℂˣ) : ℂ) := rfl
  rw [hsplit]
  have hlam : KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      ⟨aInfinity F ζ hζ u, hR⟩ = KPGlobalCenterRationalCharacter.omegaA F ζ hζ c :=
    KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ _ 1 c
      (by rw [map_one, one_mul]; exact hc)
  rw [hlam, hχc]
  have hpc : ((KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ c.val) : ℂˣ) : ℂ) =
      (((KPGlobalCenterRationalCharacter.nu F ζ hζ c.val : ℝ≥0) : ℝ) : ℂ) := rfl
  have hnu : ((KPGlobalCenterRationalCharacter.nu F ζ hζ c.val : ℝ≥0) : ℝ) =
      Real.exp ((1 / 6 : ℝ) * (2 * ∑ v, u v)) := by
    rw [hcE]; exact nu_arch F ζ hζ u
  have hnuC : (((KPGlobalCenterRationalCharacter.nu F ζ hζ c.val : ℝ≥0) : ℝ) : ℂ) =
      Complex.exp (((1 : ℂ) / 6) * ((2 * ∑ v, u v : ℝ) : ℂ)) := by
    rw [hnu, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hnormc : ((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
      (aInfinity F ζ hζ u) : ℂˣ) : ℂ) =
      Complex.exp (s * ((2 * ∑ v, u v : ℝ) : ℂ)) := by
    have hp : ((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (aInfinity F ζ hζ u) : ℂˣ) : ℂ) =
        KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s (aInfinity F ζ hζ u) := rfl
    rw [hp, KPGlobalTorusBorelTwistCompatibility.normPower, aInfinity_delta, Real.log_exp]
  rw [hpc, hnuC, hnormc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem flatR_covariance (s : ℂ) (u : InfinitePlace F → ℝ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (KPContFlatSourceRecipe.flatR F ζ hζ s f).val
      ((aInfinity F ζ hζ u).val * g) =
        Complex.exp (((4 : ℂ) / 3 + 2 * s) * ((∑ v, u v : ℝ) : ℂ)) *
          (KPContFlatSourceRecipe.flatR F ζ hζ s f).val g := by
  have hN0 : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    map_one (KPGlobalTorusFunctionData.Nhom F ζ hζ)
  have halpha : KPContFlatSourceRecipe.alpha F ζ hζ
      ((aInfinity F ζ hζ u).val * g) =
      Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ)) +
        KPContFlatSourceRecipe.alpha F ζ hζ g := by
    have h := KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ (aInfinity F ζ hζ u) 0 g
    rwa [hN0, mul_one] at h
  have hlogδ : Real.log
      (((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : ℝ≥0) : ℝ)) =
      2 * ∑ v, u v := by
    rw [aInfinity_delta F ζ hζ u, Real.log_exp]
  have halpha' : KPContFlatSourceRecipe.alpha F ζ hζ
      ((aInfinity F ζ hζ u).val * g) = (2 * ∑ v, u v) +
        KPContFlatSourceRecipe.alpha F ζ hζ g := by
    rw [halpha, hlogδ]
  have hfmem : aInfinity F ζ hζ u ∈
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H :=
    aInfinity_mem_source F ζ hζ 0 u
  let hEl : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H :=
    ⟨aInfinity F ζ hζ u, hfmem⟩
  have hElv : hEl.val = aInfinity F ζ hζ u := rfl
  have hf : f.val.val ((aInfinity F ζ hζ u).val * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ hEl.val *
        (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character
          hEl : ℂˣ) : ℂ) * f.val.val g := by
    have h := f.val.property hEl 0 g
    rwa [hN0, mul_one] at h
  have hdh : KPGlobalTorusFunctionData.deltaHalf F ζ hζ hEl.val =
      (Real.exp (∑ v, u v) : ℂ) := by
    rw [hElv, KPGlobalTorusFunctionData.deltaHalf, aInfinity_delta F ζ hζ u]
    congr 1
    rw [show Real.exp (2 * ∑ v, u v) = Real.exp (∑ v, u v) ^ 2 by
      rw [← Real.exp_nat_mul]; norm_num]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hchi : (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character
        hEl : ℂˣ) : ℂ) =
      Complex.exp (((1 : ℂ) / 6) * ((2 * ∑ v, u v : ℝ) : ℂ)) := by
    have h := source_character F ζ hζ 0 u
    rw [show (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character
        (sourceElement F ζ hζ 0 u) =
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character
        hEl from rfl] at h
    simpa using h
  calc (KPContFlatSourceRecipe.flatR F ζ hζ s f).val ((aInfinity F ζ hζ u).val * g)
      = Complex.exp (s * ((2 * ∑ v, u v : ℝ) : ℂ) +
            s * ((KPContFlatSourceRecipe.alpha F ζ hζ g : ℝ) : ℂ)) *
          (Complex.exp ((∑ v, u v : ℝ) : ℂ) *
            Complex.exp (((1 : ℂ) / 6) * ((2 * ∑ v, u v : ℝ) : ℂ)) * f.val.val g) := by
        rw [KPContFlatSourceRecipe.flatR_formula, halpha', hf, hdh, hchi,
          Complex.ofReal_exp, Complex.ofReal_add, mul_add, Complex.exp_add]
    _ = Complex.exp (((4 : ℂ) / 3 + 2 * s) * ((∑ v, u v : ℝ) : ℂ)) *
          (Complex.exp (s * ((KPContFlatSourceRecipe.alpha F ζ hζ g : ℝ) : ℂ)) *
            f.val.val g) := by
        rw [show Complex.exp (((4 : ℂ) / 3 + 2 * s) * ((∑ v, u v : ℝ) : ℂ)) *
              (Complex.exp (s * ((KPContFlatSourceRecipe.alpha F ζ hζ g : ℝ) : ℂ)) *
                f.val.val g) =
              Complex.exp (((4 : ℂ) / 3 + 2 * s) * ((∑ v, u v : ℝ) : ℂ) +
                s * ((KPContFlatSourceRecipe.alpha F ζ hζ g : ℝ) : ℂ)) *
                f.val.val g from by
          rw [← mul_assoc, ← Complex.exp_add]]
        rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
        apply congrArg (fun z => Complex.exp z * f.val.val g)
        push_cast
        ring
    _ = Complex.exp (((4 : ℂ) / 3 + 2 * s) * ((∑ v, u v : ℝ) : ℂ)) *
          (KPContFlatSourceRecipe.flatR F ζ hζ s f).val g := by
        rw [KPContFlatSourceRecipe.flatR_formula]

theorem complexDimension_eq (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    Module.finrank ℚ F / 2 = InfinitePlace.nrComplexPlaces F :=
  (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm

theorem complexDimension_eq_card (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    Module.finrank ℚ F / 2 = Fintype.card (InfinitePlace F) := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).1, zero_add]
  exact complexDimension_eq F ζ hζ

theorem complexDimension_pos (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    0 < Module.finrank ℚ F / 2 := by
  rw [complexDimension_eq F ζ hζ]
  exact (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2

theorem flatR_mean_height (s : ℂ) (t : ℝ) (b : InfinitePlace F → ℝ)
    (hb : ∑ v, b v = 0)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (KPContFlatSourceRecipe.flatR F ζ hζ s f).val
      ((aInfinity F ζ hζ (fun v => t + b v)).val * g) =
        KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t *
          (KPContFlatSourceRecipe.flatR F ζ hζ s f).val g := by
  rw [flatR_covariance F ζ hζ s (fun v => t + b v) f g]
  congr 1
  rw [KPIncomingCasimir.heightFactor]
  congr 1
  have hsum : (∑ v, (t + b v)) = (Fintype.card (InfinitePlace F) : ℝ) * t := by
    rw [Finset.sum_add_distrib, hb, add_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hsum]
  have hd : ((Module.finrank ℚ F / 2 : ℕ) : ℂ) =
      ((Fintype.card (InfinitePlace F) : ℕ) : ℂ) := by
    rw [complexDimension_eq_card F ζ hζ]
  rw [hd]
  push_cast
  ring

end DedekindZetaZeroFree.KPContFlatArchDiagonalMultiplier

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
