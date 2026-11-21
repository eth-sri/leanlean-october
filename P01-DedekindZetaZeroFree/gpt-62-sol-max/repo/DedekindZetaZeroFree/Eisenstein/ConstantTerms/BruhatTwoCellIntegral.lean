module

public import DedekindZetaZeroFree.Eisenstein.Residues.AdelicChamberContinuationData
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped NumberField ENNReal

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

namespace BruhatIntegral

variable (F : Type) [Field F] [NumberField F]

 abbrev A := NumberField.AdeleRing (𝓞 F) F
 abbrev Q := A F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

theorem integral_period_of_integrable
    (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (h : A F → ℂ) (hmeas : Measurable h) (hint : Integrable h dx) :
    Integrable (KPChamberAdditivePeriodization.complexPeriod F h) dq ∧
      (∫ q, KPChamberAdditivePeriodization.complexPeriod F h q ∂dq) =
        ∫ a, h a ∂dx := by
  have hnorm := KPChamberAdditivePeriodization.lintegral_nonnegativePeriod
    F dx dq hcompat (fun a => ENNReal.ofReal ‖h a‖) hmeas.norm.ennreal_ofReal
  have hfinite : ∫⁻ q, KPChamberAdditivePeriodization.normPeriod F h q ∂dq < ⊤ := by
    change (∫⁻ q, KPChamberAdditivePeriodization.nonnegativePeriod F
      (fun a => ENNReal.ofReal ‖h a‖) q ∂dq) < ⊤
    rw [hnorm]
    simpa only [ofReal_norm_eq_enorm, HasFiniteIntegral] using hint.hasFiniteIntegral
  exact (KPChamberAdditivePeriodization.integral_complexPeriod
    F dx dq hcompat h hmeas hfinite).2.2

theorem constantTerm_two_cells
    {G : Type*} [Group G]
    (s : Matrix.ProjGenLinGroup (Fin 2) F →* G)
    (n : Multiplicative (A F) →* G) (fR : G → ℂ)
    (hB : KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F s fR)
    (hN : KPChamberBruhatTwoCells.ScalarUnipotentInvariant F n fR)
    (hlift : KPChamberBruhatTwoCells.CompatibleUnipotentLift F s n)
    (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (g : G)
    (hsum : ∀ q : Q F, KPGlobalEisensteinData.EisensteinSummable
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g))
    (hmeas : Measurable (fun a : A F =>
      fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)))
    (hint : Integrable (fun a : A F =>
      fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)) dx) :
    (∫ q : Q F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) ∂dq) =
      fR g + ∫ a : A F,
        fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g) ∂dx := by
  let h : A F → ℂ := fun a =>
    fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)
  have hperiod := integral_period_of_integrable F dx dq hcompat h hmeas hint
  have hformula : ∀ q : Q F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) =
        fR g + KPChamberAdditivePeriodization.complexPeriod F h q := by
    intro q
    rw [KPChamberBruhatTwoCells.eisenstein_two_cells F s fR hB]
    rw [hN]
    congr 1
    apply tsum_congr
    intro t
    simpa only [h, mul_assoc] using
      KPChamberBruhatTwoCells.open_cell_translate F s n hlift fR t (Quotient.out q) g
  simp_rw [hformula]
  rw [integral_add (integrable_const _) hperiod.1, integral_const, hperiod.2]
  simp [h]

end BruhatIntegral
end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing
namespace ActualBruhat

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export KPGlobalResidualKernel.ChamberNorm.Actual
  (rational section_unipotent_invariant rational_unipotent compatible_unipotent unsigned_weyl
    section_rational_diagonal_invariant section_signed_weyl scalar_unipotent_invariant
    scalar_rational_borel_invariant)

theorem integral_two_cells (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (dx : MeasureTheory.Measure (KPGlobalTorusFunctionData.Adeles F))
    (dq : MeasureTheory.Measure (RawAdditiveQuotient F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [MeasureTheory.IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (hsum : ∀ q : RawAdditiveQuotient F,
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F => rational F ζ hζ (Quotient.out c))
        v.val (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g))
    (hmeas : Measurable (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)))
    (hint : MeasureTheory.Integrable (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)) dx) :
    (∫ q : RawAdditiveQuotient F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => rational F ζ hζ (Quotient.out c))
      v.val (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) (hsum q) ∂dq) =
      v.val g + ∫ a : KPGlobalTorusFunctionData.Adeles F,
        v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g) ∂dx := by
  have heq : (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) *
        KPGlobalTorusFunctionData.Nhom F ζ hζ (Multiplicative.ofAdd a) * g)) =
      (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)) := by
    funext a
    change v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) *
      KPGlobalTorusFunctionData.N F ζ hζ a * g) = _
    simpa only [mul_assoc] using section_signed_weyl F ζ hζ s v
      (KPGlobalTorusFunctionData.N F ζ hζ a * g)
  have h := BruhatIntegral.constantTerm_two_cells F (rational F ζ hζ)
    (KPGlobalTorusFunctionData.Nhom F ζ hζ) v.val
    (scalar_rational_borel_invariant F ζ hζ s v)
    (scalar_unipotent_invariant F ζ hζ s v) (compatible_unipotent F ζ hζ)
    dx dq hcompat g hsum (heq.symm ▸ hmeas) (heq.symm ▸ hint)
  rw [heq] at h
  exact h

end ActualBruhat
end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

end

end
