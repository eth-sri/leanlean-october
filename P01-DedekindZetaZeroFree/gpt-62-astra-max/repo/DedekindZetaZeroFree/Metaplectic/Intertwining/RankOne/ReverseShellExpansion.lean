module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseSmallTailSignedCubeBlocks
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.InfinityTailContinuation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseShellLaurentDenominator

@[expose] public section

section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw KPActualScalarBinding
open KPRankOneReverseLaurentShellExpansion KPActualResidueSources
noncomputable section
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)

theorem actual_small_tail_specialization :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      MeasurableSet (smallRegion F q N) ∧
      ∃ p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator,
        ∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ, ConvergenceRegion F q r lam →
          ∀ h : KPExceptionalRaw.actualTorus F ζ hζ q,
          IntegrableOn
            (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h)
            (smallRegion F q N) (multiplicativeMeasure F q μ) ∧
          (∫ v in smallRegion F q N,
            reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
            evaluateNumerator (p h) r (Q F q lam) /
              ((1 - t F q r) * smallFactor F q r (Q F q lam)) := small_tail_shells F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
    rep hrep d φ hφ hcφ

theorem actual_finite_annulus_specialization (N : ℕ) :
    MeasurableSet (annulusRegion F q N) ∧
      ∃ p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator,
        ∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ,
          ∀ h : KPExceptionalRaw.actualTorus F ζ hζ q,
          IntegrableOn
            (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h)
            (annulusRegion F q N) (multiplicativeMeasure F q μ) ∧
          (∫ v in annulusRegion F q N,
            reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
            evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r) := by
  obtain ⟨L, χ, _, hL, hforward, _⟩ := actual_forward_uniform_infinity_data
    F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
  obtain ⟨E, c, hc, hexp⟩ := FiniteAnnulusSteps.reverse_compact_laurent_annulus
    F ζ hζ q S.heisenberg S.borel P I μ (S.openCell P) L hL χ N
  have hmeas : MeasurableSet (annulusRegion F q N) := by
    letI : BorelSpace (LocalField F q)ˣ := ⟨by
      rw [@BorelSpace.measurable_eq (LocalField F q) _ _ _,
        Units.isEmbedding_val₀.isInducing.eq_induced]
      exact borel_comap.symm⟩
    exact (FiniteAnnulusSteps.reverse_compact_valuationIndex_locallyConstant F q).continuous.measurable measurableSet_Icc
  refine ⟨hmeas, fun h => integratedShellNumerator
    ((multiplicativeMeasure F q μ).restrict (annulusRegion F q N)) E (c h), ?_⟩
  intro r hr lam h
  apply setIntegral_finite_shell_expansion (multiplicativeMeasure F q μ)
    (annulusRegion F q N) hmeas E (c h) (hc h) (r : ℂ) (Q F q lam)
    (1 - t F q (r : ℂ))
    (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
      rep hrep d φ hφ hcφ r lam h)
  intro v hv
  simpa only [FiniteAnnulusSteps.reverseCompactLaurentIntegrand, reverseIntegrand,
    hforward r hr] using hexp r hr lam h v hv

end
end DedekindZetaZeroFree.KPActualResidueSources

end

section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw KPActualScalarBinding
open KPRankOneReverseLaurentShellExpansion
noncomputable section
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)

private theorem infinity_factor_ne_zero (lam : ℂ) (hlam : lam.re < 1) :
    infinityFactor F q (Q F q lam) ≠ 0 := by
  let residueCardinality₀ := residueCardinality (LocalField F q)
  have hq : 0 < (residueCardinality₀ : ℝ) := by
    exact_mod_cast (Nat.card_pos)
  have hnormQ : ‖Q F q lam‖ = (residueCardinality₀ : ℝ).rpow (-lam.re) := by
    simp only [Q, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_eq_pow,
      Real.rpow_def_of_pos hq]
    congr 1
    ring
  have hn : ‖(residueCardinality₀ : ℂ) ^ (-3 : ℤ) *
      Q F q lam ^ (-3 : ℤ)‖ =
      (residueCardinality₀ : ℝ).rpow (3 * lam.re - 3) := by
    rw [norm_mul, norm_zpow, norm_zpow, hnormQ]
    have hnat : ‖(residueCardinality₀ : ℂ)‖ =
        (residueCardinality₀ : ℝ) := by simp
    rw [hnat, Real.rpow_eq_pow, ← Real.rpow_intCast, ← Real.rpow_intCast,
      ← Real.rpow_mul hq.le, ← Real.rpow_add hq, Real.rpow_eq_pow]
    congr 1
    norm_num
    ring
  have hlt : ‖(residueCardinality₀ : ℂ) ^ (-3 : ℤ) *
      Q F q lam ^ (-3 : ℤ)‖ < 1 := by
    rw [hn, Real.rpow_eq_pow]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast Finite.one_lt_card
    · linarith
  intro he
  rw [((sub_eq_zero.mp he).symm), norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem infinity_region_measurable (N : ℕ) :
    MeasurableSet (infinityRegion F q N) := by
  letI : BorelSpace (LocalField F q)ˣ := ⟨by
    rw [@BorelSpace.measurable_eq (LocalField F q) _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced]
    exact borel_comap.symm⟩
  exact (FiniteAnnulusSteps.reverse_compact_valuationIndex_locallyConstant F q).continuous.measurable measurableSet_Ioi

private theorem regions_union (N : ℕ) :
    (smallRegion F q N ∪ annulusRegion F q N) ∪ infinityRegion F q N = Set.univ := by
  ext v
  simp only [Set.mem_union, smallRegion, annulusRegion, infinityRegion,
    Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega

private theorem regions_disjoint (N : ℕ) :
    Disjoint (smallRegion F q N) (annulusRegion F q N) ∧
    Disjoint (smallRegion F q N ∪ annulusRegion F q N) (infinityRegion F q N) := by
  constructor <;> rw [Set.disjoint_left] <;> intro v hv hw
  · simp only [smallRegion, annulusRegion, Set.mem_setOf_eq] at hv hw
    omega
  · simp only [Set.mem_union, smallRegion, annulusRegion, infinityRegion,
      Set.mem_setOf_eq] at hv hw
    omega

theorem actual_reverse_shell_expansion :
    ∃ p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator,
      ∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ,
        ConvergenceRegion F q r lam → ∀ h : KPExceptionalRaw.actualTorus F ζ hζ q,
        Integrable (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J
          (S.openCell P) rep hrep d φ hφ hcφ r lam h) (multiplicativeMeasure F q μ) ∧
        H F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
          rep hrep d φ hφ hcφ r lam h =
          evaluateNumerator (p h) r (Q F q lam) /
            shellDenominator F q r (Q F q lam) := by
  classical
  obtain ⟨N₀, hs⟩ := actual_small_tail_specialization F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ
  obtain ⟨NInf, hi⟩ := actual_infinity_tail_specialization F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ
  let N := max N₀ NInf
  obtain ⟨hms, p₀, hp₀⟩ := hs N (le_max_left _ _)
  obtain ⟨hmA, pA, hpA⟩ := actual_finite_annulus_specialization F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ N
  obtain ⟨pInf, hpInf⟩ := hi N (le_max_right _ _)
  choose p hp using fun h : KPExceptionalRaw.actualTorus F ζ hζ q =>
    combine_laurent_shell_numerators F q (p₀ h) (pA h) (pInf h)
  refine ⟨p, ?_⟩
  intro r hr lam hlam h
  obtain ⟨hsint, hsval⟩ := hp₀ r hr lam hlam h
  obtain ⟨haint, haval⟩ := hpA r hr lam h
  obtain ⟨hiint, _, _, hival⟩ := hpInf r hr lam hlam.1 h
  have hall := (hsint.union haint).union hiint
  rw [regions_union F q N, integrableOn_univ] at hall
  obtain ⟨hdisA, hdisInf⟩ := regions_disjoint F q N
  have hsum := setIntegral_union hdisInf (infinity_region_measurable F q N)
    (hsint.union haint) hiint
  rw [setIntegral_union hdisA hmA hsint haint] at hsum
  rw [regions_union F q N, setIntegral_univ] at hsum
  change H F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r lam h = _ at hsum
  rw [hsval, haval, hival] at hsum
  exact ⟨hall, hsum.trans (hp h (r : ℂ) (Q F q lam) r.ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero hr (KPRankOneReverseLaurentShellExpansion.smallTail_factor_ne_zero F q r lam hlam)) (infinity_factor_ne_zero F q lam hlam.1))).symm⟩

end
end DedekindZetaZeroFree.KPActualResidueSources

end
