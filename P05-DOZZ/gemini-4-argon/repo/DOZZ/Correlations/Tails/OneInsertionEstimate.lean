/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CanonicalLeadingTail
public import DOZZ.Correlations.Tails.UniformCutMoments
public import DOZZ.Correlations.Tails.LocalizationData
public import DOZZ.Correlations.Tails.TotalCopiedRemainder
public import DOZZ.Correlations.Tails.TwoSpaceTailSandwich
public import DOZZ.Correlations.Tails.UniformTailSandwich
public import DOZZ.Correlations.Tails.ENNRealPowerTail

/-! The original one-insertion estimate from its localized copied law and bounded remainders. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem oneInsertion_estimate_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (M : Ω → Measure ℂ) γ (hγ : 0 < γ) (hγ2 : γ < 2) (hM : IsGMCOf P X γ M)
    Kz (hKz : IsCompact Kz) (hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    Kα (hKα : IsCompact Kα) (hα : ∀ α ∈ Kα, γ/2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) radius supBound derivBound lowerBound
    (hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hData : ∀ α ∈ Kα, IsReflectionData P γ α (B α) Z)
    η (hη : 0 < η) (hceil : ∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
      |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal-
        oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z)*
          x^(-reflectionExponent γ α)| ≤ C*x^(-reflectionExponent γ α-η) := by
  let : IsProbabilityMeasure P := hX.1
  rcases Kα.eq_empty_or_nonempty with he | hn
  · refine ⟨0,le_rfl,?_⟩
    intro z hzk α hαk
    simp only [he,mem_empty_iff_false] at hαk
  obtain ⟨a,r,R,g,pH,qH,hηa,ha1,hR,hRbulk,hg,hpq,hcuts⟩ :=
    uniform_oneInsertion_cut_moments γ hγ Kα hKα hn hα η hη hceil
  have ha0 := hη.trans hηa
  obtain ⟨αA,hαA,hAmax⟩ := hKα.exists_isMaxOn hn continuous_abs.continuousOn
  let A := |αA|
  have hA (α : ℝ) (hαk : α ∈ Kα) := (le_abs_self α).trans (hAmax hαk)
  have hAmax α (hαk : α ∈ Kα) : |α-1/γ| ≤ A+|1/γ| :=
    (show |α-1/γ| ≤ |α|+|1/γ| by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le α 0 (1/γ)).trans
        (add_le_add (hAmax hαk) le_rfl)
  let ρ := min radius 1/2
  have hρ : 0 < ρ := div_pos (lt_min hFamily.1 zero_lt_one) (by norm_num)
  have hρR : ρ ≤ min radius 1 := by dsimp [ρ]; linarith only [lt_min hFamily.1 zero_lt_one]
  obtain ⟨χ,hχc,hχ,hχs,hχone⟩ := localization_bump ρ hρ
  obtain ⟨E,hE,hLead⟩ := canonical_leading_tail_uniform P X Xc hX hc hm hcont
    γ hγ hγ2 Kz hKz hz Kα hKα hα B Z hZ hData supBound R η a hFamily.2.1 hR hRbulk
    hη hηa r (fun α hαk => ⟨(hcuts α hαk).1,(hcuts α hαk).2.1⟩)
    (fun α hαk => (hcuts α hαk).2.2.1)
  obtain ⟨D₁,hD₁,hOrig⟩ := annular_remainder_moment_uniform P X hX γ hγ hγ2 M hM
    Kz hKz (ρ/4) A supBound R (by positivity) (by linarith only [hρR.trans (min_le_right _ _),hρ]) hFamily.2.1 hR hRbulk
  obtain ⟨D₂,hD₂,hCopy⟩ := total_copied_remainder_uniform P X Xc hX hc γ hγ hγ2 M hM
    Kz hKz hz Family radius supBound derivBound lowerBound hFamily ρ hρ hρR
    A (A+|1/γ|) g R pH qH hg hR hRbulk hpq
  let C := (2+E)*2^(R+η)+E*2^(R+η)+(1+E)*R*2^(R+1)+(D₁.toReal+D₂.toReal)*4^R
  refine ⟨C,(by dsimp [C]; positivity),?_⟩
  intro z hzk α hαk F hF x hx
  obtain ⟨N,hN,_⟩ := translated_source_gmc_exists P X Xc hX hc z (hz z hzk)
    γ hγ hγ2 M hM
  obtain ⟨hFm,hFb,hFl,_,_⟩ := hFamily.2.2.2.2 z hzk F hF
  have hFz := hFamily.2.2.2.1.trans_le hFl
  have hα0 := (div_pos hγ (by norm_num : (0 : ℝ) < 2)).le.trans (hα α hαk).1.le
  obtain ⟨hr,hrR,hpr,hmargin⟩ := hcuts α hαk
  have hins : r α*qH+g ≤ 2/γ*(Q γ-(α-1/γ)) := by
    have hi : reflectionExponent γ α+2/γ^2 = 2/γ*(Q γ-(α-1/γ)) := by
      unfold reflectionExponent
      field_simp
      ring
    rw [← hi]
    exact hmargin.trans (min_le_left _ _)
  have hCopyMoment := hCopy z hzk F hF N hN α (r α) hα0 (hA α hαk) (hAmax α hαk) hr hrR (hmargin.trans (min_le_right _ _)) hins
  change AEMeasurable (copiedRemainder N Xc F z γ α ρ) (P.prod P) ∧
    (∫⁻ q, copiedRemainder N Xc F z γ α ρ q^(r α) ∂P.prod P) ≤ D₂ at hCopyMoment
  obtain ⟨hLaw,hLm,hLcm,hEm,hEcm,hSource,hCopied⟩ :=
    localized_insertion_comparison_data P X Xc hX hc hm γ hγ hγ2 M hM
      Kz Family radius supBound derivBound lowerBound hFamily z hzk (hz z hzk) F hF
      N hN α ρ hα0 hρ hρR χ hχc hχ hχs hχone
  let T := fun t => (P {ω | ENNReal.ofReal t < localSingularMass M F z γ α ω}).toReal
  let L := fun t => ((P.prod P) {q | ENNReal.ofReal t < canonicalLeading N Xc (F z) z γ α q}).toReal
  let c := oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z)
  have hL t (ht : 1 ≤ t) : |L t-c*t^(-reflectionExponent γ α)| ≤ E*t^(-reflectionExponent γ α-η) :=
    hLead z hzk α hαk (F z) hFz ((le_abs_self _).trans (hFb z).2) N hN t ht
  have hT t (_ : 1 ≤ t) : 0 ≤ T t ∧ T t ≤ 1 := by
    constructor
    · exact ENNReal.toReal_nonneg
    · change (P {ω | ENNReal.ofReal t < localSingularMass M F z γ α ω}).toReal ≤ 1
      exact measureReal_le_one
  have hcc : c ≤ 1+E := by
    have ht := (abs_le.mp (hL 1 le_rfl)).1
    simp only [Real.one_rpow,mul_one] at ht
    linarith only [ht,(show L 1 ≤ 1 by change ((P.prod P) {q | ENNReal.ofReal 1 < canonicalLeading N Xc (F z) z γ α q}).toReal ≤ 1; exact measureReal_le_one)]
  have hSand t (ht : 2 ≤ t) :
      let h := t^(1-a)/4
      L (t+h)-D₂.toReal*h^(-(r α)) ≤ T t ∧
      T t ≤ L (t-2*h)+(D₁.toReal+D₂.toReal)*h^(-(r α)) := by
    dsimp only
    have hsize := polynomial_shift_size t a ((by norm_num : (1 : ℝ) ≤ 2).trans ht) ha0.le
    have hs := two_space_localization_tail_sandwich P (P.prod P)
      (localSingularMass M F z γ α) (localizedOriginal M χ F z γ α)
      (originalAnnular M F z γ α (ρ/4))
      (canonicalLeading N Xc (F z) z γ α) (localizedCopy N Xc χ F z γ α)
      (copiedRemainder N Xc F z γ α ρ) hLm hLcm hLaw hSource hCopied t
      (t^(1-a)/4) hsize.1.le (by linarith only [hsize.2.1,ht])
    have h₂ := ennreal_power_tail_le_moment (P.prod P) (copiedRemainder N Xc F z γ α ρ)
      hEcm (r α) (t^(1-a)/4) hr hsize.1 D₂ hD₂ hCopyMoment.2
    constructor
    · dsimp only [L,T] at *
      linarith only [hs.1,h₂]
    · rw [add_mul]
      dsimp only [L,T] at *
      linarith only [hs.2,(ennreal_power_tail_le_moment P (originalAnnular M F z γ α (ρ/4)) hEm (r α) (t^(1-a)/4) hr hsize.1 D₁ hD₁ (hOrig z hzk α (r α) hα0 (hA α hαk) hr hrR F (fun y => ⟨(hFb y).1,(le_abs_self _).trans (hFb y).2⟩))),h₂]
  simpa only [T,c,C,(show (1 : ℝ)+(1+E) = 2+E by ring)] using (uniform_tail_sandwich_bound T L (reflectionExponent γ α) R η a (r α) R c (1+E) E D₁.toReal D₂.toReal ((residue_critical_order_bounds γ α hγ (hα α hαk).1 (hα α hαk).2).1).le (by nlinarith only [hpr,hr,hrR,ha0,hη]) hη hηa.le hrR hpr.le (by unfold c oneInsertionTailCoefficient reflectionBarR; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (Real.rpow_nonneg hFz.le _)) ENNReal.toReal_nonneg) hcc hE ENNReal.toReal_nonneg ENNReal.toReal_nonneg hT hL hSand x hx)


end DOZZ.Proofs
