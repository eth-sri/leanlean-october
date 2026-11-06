module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Cubic.AllCuspProjection
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.KernelTorus.AdelicPeriodIdentity
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ArchimedeanWeylCovariance
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.AllCuspSource
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chambers.OutgoingL2Data

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberOutgoingAdapter

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Cusps := KPContActualAllCuspSource.Cusps F ζ hζ C R P H U
abbrev d := KPCuspLogShape.dimension F
abbrev V : Set ℂ := KPContActualChamberNormalSeries.V

theorem exponent_margin (s : ℂ) (hs : s ∈ V) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(d F : ℝ) * t) * ‖KPChamberOutgoingL2.outgoingFactor (d F) s t‖ ≤
      Real.exp (-(d F : ℝ) * t) := by
  have hc : 0 ≤ (d F : ℝ) := Nat.cast_nonneg _
  have hs' : (1 : ℝ) / 3 < s.re := hs
  have he : ‖KPChamberOutgoingL2.outgoingFactor (d F) s t‖ ≤ 1 := by
    rw [KPChamberOutgoingL2.outgoingFactor, Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have hex : ((d F : ℂ) * ((2 / 3 : ℂ) - 2 * s) * (t : ℂ)).re =
        (d F : ℝ) * (2 / 3 - 2 * s.re) * t := by simp
    rw [hex]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hc (by linarith)) ht
  exact mul_le_of_le_one_right (Real.exp_nonneg _) he

variable (a : Cusps F ζ hζ C R P H U)

abbrev geometry := KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a
abbrev KernelTorus := KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a
abbrev ZeroFiber := KPContFlatCuspIncomingEvaluation.ZeroFiber F ζ hζ C R P H U a

def endMeasure : Measure (KPCuspCharts.Coordinates F) :=
  (H.disintegration (level F ζ hζ C R P H U)).componentWeight a.1 •
    (((volume.prod (geometry F ζ hζ C R P H U a).shapeMeasure).prod
      (KPCuspCharts.radialMeasure (d F))).restrict
        {p | p.1 ∈ (geometry F ζ hζ C R P H U a).fundamentalDomain})

def tail (A : ℝ) : Set (KPCuspCharts.Coordinates F) := {p | A < p.2}

theorem end_exponential_mass_finite (κ : ℝ) (hκ : κ < 2*(d F : ℝ)) (A : ℝ) :
    (∫⁻ p in tail F A, ENNReal.ofReal (Real.exp (κ*p.2))
      ∂endMeasure F ζ hζ C R P H U a) < (⊤ : ℝ≥0∞) := by
  let G := geometry F ζ hζ C R P H U a
  let μ : Measure (KPCuspCharts.Cross F) :=
    (volume : Measure (KPCuspCharts.Horizontal F)).prod G.shapeMeasure
  let D := G.fundamentalDomain
  let ν := KPCuspCharts.radialMeasure (d F)
  let w := (H.disintegration (level F ζ hζ C R P H U)).componentWeight a.1
  have hrad : (∫⁻ t in Set.Ioi A, ENNReal.ofReal (Real.exp (κ*t)) ∂ν) < (⊤ : ℝ≥0∞) := by
    dsimp [ν, KPCuspCharts.radialMeasure]
    rw [restrict_withDensity measurableSet_Ioi]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    have he : (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * t)) *
        ENNReal.ofReal (Real.exp (κ*t))) =
        (fun t => ENNReal.ofReal (Real.exp ((κ-2*(KPCuspLogShape.dimension F : ℝ))*t))) := by
      funext t
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    simp only [Pi.mul_apply]
    rw [he, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_mul_Ioi (by linarith : κ-2*(KPCuspLogShape.dimension F : ℝ) < 0) A)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_lt_top
  letI := KPCompactGreen.fundamentalDomain_finiteMeasure G
  have hμ : μ D < (⊤ : ℝ≥0∞) := by
    change (volume.prod G.shapeMeasure) G.fundamentalDomain < (⊤ : ℝ≥0∞)
    rw [← Measure.restrict_apply_univ G.fundamentalDomain]
    exact measure_lt_top _ _
  letI := G.haar_shapeMeasure
  letI : SFinite μ := by dsimp [μ]; infer_instance
  letI : SFinite ν := by dsimp [ν, KPCuspCharts.radialMeasure]; infer_instance
  have hm : ((μ.prod ν).restrict {p : KPCuspCharts.Coordinates F | p.1 ∈ D}).restrict
      {p | A < p.2} = (μ.restrict D).prod (ν.restrict (Set.Ioi A)) := by
    have ht : MeasurableSet {p : KPCuspCharts.Coordinates F | A < p.2} :=
      measurableSet_Ioi.preimage measurable_snd
    rw [Measure.restrict_restrict ht, Measure.prod_restrict]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioi]
    exact and_comm
  change (∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2},
    ENNReal.ofReal (Real.exp (κ*p.2)) ∂w • ((μ.prod ν).restrict {p | p.1 ∈ D})) < (⊤ : ℝ≥0∞)
  rw [Measure.restrict_smul, lintegral_smul_measure]
  rw [hm, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ((H.disintegration _).finite_componentWeight a.1)
    (ENNReal.mul_lt_top hrad hμ)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (f : ℂ → S)
variable (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B
  KPContinuation.spectralDomain f χ)

def correctionSheet (s : ℂ) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) : ℂ :=
  KPContActualChamberNormalSeries.E F ζ hζ U ι f s
    (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε) -
  KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
    (source.descent.cutoff s)
    (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a ε ((x,b),t))

def zeroMode (s : ℂ) (t : ℝ) (b : KPCuspCharts.Shape F) : ZeroFiber F ζ hζ C R P H U a :=
  KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
    (fun ε => ∫ z : KernelTorus F ζ hζ C R P H U a,
      correctionSheet F ζ hζ C R P H U a ι B f χ source s t (Quotient.out z) b ε
      ∂fiberMeasure F ζ hζ C R P H U a)

def standardIntegral (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  ∫ x : KPGlobalTorusFunctionData.Adeles F,
    KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) *
        KPGlobalTorusFunctionData.N F ζ hζ x * g)
    ∂KPAdditiveHaar.adelicMeasure F

def coefficient (s : ℂ) (b : KPCuspCharts.Shape F) : ZeroFiber F ζ hζ C R P H U a :=
  KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
    (fun ε => standardIntegral F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a 0 0 b ε))

theorem inverse_fixed {z c : ℂ} (hz : z ≠ 0) (h : z * c = c) : z⁻¹ * c = c := by
  calc z⁻¹ * c = z⁻¹ * (z * c) := congrArg (z⁻¹ * ·) h.symm
       _ = c := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

private theorem average_fixed {I : Type*} [Fintype I] [Nonempty I]
    (w : I → ℂ) (c : ℂ) (hw : ∀ i, w i * c = c) :
    ((Fintype.card I : ℂ)⁻¹ * ∑ i, w i) * c = c := by
  rw [mul_assoc, Finset.sum_mul]
  simp_rw [hw]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

set_option maxHeartbeats 1200000 in

theorem zeroProjection_reconstruct (v : ZeroFiber F ζ hζ C R P H U a) :
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * v.val 0) = v := by
  letI := Fintype.ofFinite (rootsOfUnity 3 F)
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).finite_deck
  letI := Fintype.ofFinite (KPContFlatCuspIncomingEvaluation.TranslationDeck F ζ hζ C R P H U a)
  letI := Fintype.ofFinite (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
    (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U))
  apply Subtype.ext
  funext z
  rw [KPContFlatCuspIncomingEvaluation.zeroProjection_formula, v.property.2 z]
  unfold KPContFlatCuspIncomingEvaluation.projectedScalar
  have hs : ((Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ * ∑ ε : rootsOfUnity 3 F,
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * v.val 0)) = v.val 0 := by
    simp only [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
  rw [hs, mul_assoc]
  rw [average_fixed (fun η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
    (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) =>
      (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹)
    (v.val 0) (fun η => inverse_fixed (Units.ne_zero _) (v.property.1.1 0 η.val η.property))]
  apply average_fixed
  intro q
  unfold KPContFlatCuspIncomingEvaluation.deckCoefficient
  apply inverse_fixed (Units.ne_zero _)
  have hv := (v.property.1.2 (Quotient.out q) 0).symm
  simpa only [v.property.2, QuotientAddGroup.mk_zero] using hv

theorem standardIntegral_height (s : ℂ) (t : ℝ) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) :
    standardIntegral F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε) =
    KPChamberOutgoingL2.outgoingFactor (d F) s t *
      standardIntegral F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a ε).val := by
  have hhorizontal : KPContinuation.ChamberFlatCasimir.horizontalAdele F ζ hζ
      (KPCuspCharts.toArch F ((0,b),t)) = 0 := by
    funext w
    simp [KPContinuation.ChamberFlatCasimir.horizontalAdele, KPCuspCharts.toArch]
    rfl
  have hheights : KPContinuation.ChamberFlatCasimir.heights F ζ hζ
      (KPCuspCharts.toArch F ((0,b),t)) =
      (fun w => t + (b : Fin (d F) → ℝ)
        (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)) := by
    funext w
    simp [KPContinuation.ChamberFlatCasimir.heights, KPCuspCharts.toArch]
  have hb : (∑ w : NumberField.InfinitePlace F, (b : Fin (d F) → ℝ)
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)) = 0 := by
    rw [Equiv.sum_comp (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ)]
    simpa [KPCuspLogShape.sumCoordinates, KPCuspLogShape.hyperplane] using b.property
  unfold standardIntegral
  rw [KPContFlatCuspIncomingEvaluation.localGroup,
    KPContinuation.ChamberFlatCasimir.iwasawa_insertion, hhorizontal]
  rw [show KPGlobalTorusFunctionData.N F ζ hζ ((0,0) : KPGlobalTorusFunctionData.Adeles F) = 1 from
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one]
  rw [one_mul]
  rw [hheights, KPContinuation.ChamberOutgoingSource.actual_forward_arch_covariance]
  congr 1
  rw [Finset.sum_add_distrib, hb, add_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← KPContFlatArchDiagonalMultiplier.complexDimension_eq_card F ζ hζ,
    KPContFlatArchDiagonalMultiplier.complexDimension_eq F ζ hζ]
  unfold KPChamberOutgoingL2.outgoingFactor d
  push_cast
  congr 1
  ring

theorem outgoing_formula (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (s : ℂ) (hs : s ∈ V) (t : ℝ) (b : KPCuspCharts.Shape F)
    (ht : T + 1 ≤ t) (hbuffer : B.τ < t) :
    zeroMode F ζ hζ C R P H U a ι B f χ source s t b =
      KPChamberOutgoingL2.outgoingFactor (d F) s t • coefficient F ζ hζ C R P H U a ι f s b := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ) / 6 < s.re
    change (1 : ℝ) / 3 < s.re at hs
    linarith
  let W := KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b
  have hcut : ∀ x ε,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s)
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a ε ((x,b),t)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * W.val 0 := by
    intro x ε
    rw [KPContActualCutoffSmoothDescent.scalar_coveredPoint,
      source.descent.cutoff_frame s hsΩ a ((x,b),t) hbuffer,
      (χ a).one_above t ht]
    simp only [Complex.ofReal_one, one_mul, KPContActualCutoffSmoothDescent.incomingValue]
    exact congrArg ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * ·) (W.property.2 _)
  letI := fiber_probability F ζ hζ C R P H U a
  have hE : ∀ ε, Integrable (fun z : KernelTorus F ζ hζ C R P H U a =>
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε))
      (fiberMeasure F ζ hζ C R P H U a) := by
    intro ε
    simpa only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
      iteratedDerivWithin_zero] using
      KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_integrable
        F ζ hζ C R P H U ι hι f hf a s hs t b ε
  have hdiff : (fun ε => ∫ z : KernelTorus F ζ hζ C R P H U a,
      correctionSheet F ζ hζ C R P H U a ι B f χ source s t (Quotient.out z) b ε
      ∂fiberMeasure F ζ hζ C R P H U a) =
      (fun ε => ∫ z : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s
          (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε)
        ∂fiberMeasure F ζ hζ C R P H U a) -
      (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * W.val 0) := by
    funext ε
    unfold correctionSheet
    simp_rw [hcut]
    rw [integral_sub (hE ε) (integrable_const _)]
    simp
  unfold zeroMode
  rw [hdiff, map_sub, zeroProjection_reconstruct,
    KPContinuation.ChamberOutgoingSource.actual_projected_kernel_period_eq F ζ hζ C R P H U ι f hι hf s hs a t b,
    KPContinuation.ChamberOutgoingSource.actual_projected_upper_constantTerm_eq F ζ hζ C R P H U ι f hι hf s hs a t b]
  rw [← KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hsΩ (f s) t b]
  change W + _ - W = _
  rw [add_sub_cancel_left]
  have hforward : (fun ε => standardIntegral F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)) =
      KPChamberOutgoingL2.outgoingFactor (d F) s t •
      (fun ε => standardIntegral F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a 0 0 b ε)) := by
    funext ε
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [standardIntegral_height F ζ hζ C R P H U a ι f s t b ε,
      standardIntegral_height F ζ hζ C R P H U a ι f s 0 b ε]
    simp [KPChamberOutgoingL2.outgoingFactor]
  change KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
    (fun ε => standardIntegral F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)) = _
  rw [hforward, map_smul]
  rfl

theorem coefficient_shape_constant (s : ℂ) (b c : KPCuspCharts.Shape F) :
    coefficient F ζ hζ C R P H U a ι f s b = coefficient F ζ hζ C R P H U a ι f s c := by
  unfold coefficient
  congr 1
  funext ε
  rw [standardIntegral_height F ζ hζ C R P H U a ι f s 0 b ε,
    standardIntegral_height F ζ hζ C R P H U a ι f s 0 c ε]

private theorem integral_extension {B T : Type*}
    [TopologicalSpace B] [CompactSpace B] [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ]
    (π : C(B,T)) (hπ : Function.Surjective π) :
    ∃ I : C(B,ℂ) →L[ℂ] ℂ, ∀ u : C(T,ℂ), I (u.comp π) = ∫ q, u q ∂μ := by
  let J : C(T,ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun u => ∫ q, u q ∂μ
      map_add' := fun u v => integral_add
        (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c u => integral_smul c u }
    1 (by
      intro u
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (u.norm_coe_le_norm)))
  let j : C(T,ℂ) →ₗᵢ[ℂ] C(B,ℂ) :=
    { toLinearMap := (ContinuousMap.compCLM ℂ ℂ π).toLinearMap
      norm_map' := by
        intro u
        apply le_antisymm
        · exact (ContinuousMap.norm_le _ (norm_nonneg u)).mpr (fun x => u.norm_coe_le_norm (π x))
        · exact (ContinuousMap.norm_le _ (norm_nonneg (u.comp π))).mpr (fun q => by
            obtain ⟨x, rfl⟩ := hπ q
            exact (u.comp π).norm_coe_le_norm x) }
  obtain ⟨I,hI,_⟩ := exists_extension_norm_eq j.toLinearMap.range
    (J.comp j.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨I, fun u => ?_⟩
  have h := hI (j.equivRange u)
  have hi : (j.equivRange u).val = u.comp π := by
    rw [LinearIsometry.equivRange_apply_coe]; rfl
  have hj : (J.comp j.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap) (j.equivRange u) = J u := by
    change J (j.equivRange.symm (j.equivRange u)) = J u
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hi, hj] at h
  exact h

private theorem kernel_integral_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    DifferentiableOn ℂ (fun s => ∫ z : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε)
      ∂fiberMeasure F ζ hζ C R P H U a) V := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := fiber_probability F ζ hζ C R P H U a
  obtain ⟨B,hB,hrep⟩ := KPContinuation.ChamberModerateGrowth.compact_kernel_representatives F ζ hζ C R P H U a
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let π : C(B,KernelTorus F ζ hζ C R P H U a) :=
    ⟨fun x => QuotientAddGroup.mk x.val, QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩
  have hπ : Function.Surjective π := fun q => by
    obtain ⟨x,hx,he⟩ := hrep q
    exact ⟨⟨x,hx⟩,he⟩
  obtain ⟨I,hI⟩ := integral_extension (fiberMeasure F ζ hζ C R P H U a) π hπ
  let c : KPCuspCharts.Horizontal F → KPContActualChamberNormalSeries.G F ζ hζ :=
    fun x => KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε
  have hc : Continuous c := by
    have harch : Continuous (fun x : KPCuspCharts.Horizontal F => KPCuspCharts.toArch F ((x,b),t)) :=
      (KPCuspCharts.toArch_contDiff F).continuous.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    have hsec := (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp harch
    have hins := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp hsec
    exact continuous_const.mul (hins.mul continuous_const)
  let A := c '' B
  have hA : IsCompact A := hB.image hc
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cB : C(B,A) := ⟨fun x => ⟨c x.val, ⟨x.val,x.property,rfl⟩⟩,
    (hc.comp continuous_subtype_val).subtype_mk _⟩
  let g : ℂ → C(B,ℂ) := fun s =>
    (KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf 0 [] A s).comp cB
  have hg : DifferentiableOn ℂ g V :=
    (ContinuousMap.compCLM ℂ ℂ cB).differentiable.comp_differentiableOn
      (KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A hA)
  apply (I.differentiable.comp_differentiableOn hg).congr
  intro s hs
  let u : C(KernelTorus F ζ hζ C R P H U a,ℂ) :=
    ⟨fun q => KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out q) b ε), by
      simpa only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
        iteratedDerivWithin_zero] using
        KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_continuous F ζ hζ C R P H U ι hι f hf a s hs t b ε⟩
  have he : g s = u.comp π := by
    ext x
    have hp := KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative F ζ hζ C R P H U
      ι hι f hf a s hs t x.val (Quotient.out (π x)) b ε (Quotient.out_eq (π x)).symm
    simpa [g, KPContActualChamberNormalSeries.compactMixedJet, hs, cB, c,
      KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
      KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet, u] using hp
  change (∫ z, u z ∂fiberMeasure F ζ hζ C R P H U a) = I (g s)
  rw [he]
  exact (hI u).symm

theorem coefficient_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (b : KPCuspCharts.Shape F) :
    DifferentiableOn ℂ (fun s => (coefficient F ζ hζ C R P H U a ι f s b).val 0) V := by
  letI := Fintype.ofFinite (rootsOfUnity 3 F)
  let J : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun e => (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a e).val 0
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  let L := J.toContinuousLinearMap
  have he : DifferentiableOn ℂ (fun s ε => ∫ z : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a 0 (Quotient.out z) b ε)
      ∂fiberMeasure F ζ hζ C R P H U a) V :=
    differentiableOn_pi.mpr (fun ε => kernel_integral_holomorphic F ζ hζ C R P H U a ι f hι hf 0 b ε)
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro s hs
    change -(1 : ℝ) / 6 < s.re
    change (1 : ℝ) / 3 < s.re at hs
    linarith
  have hin : DifferentiableOn ℂ (fun s =>
      (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
        (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s))).val 0) V := by
    have hi : DifferentiableOn ℂ (fun s =>
        KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s)) V := by
      apply differentiableOn_pi.mpr
      intro ε
      let ev : S →ₗ[ℂ] ℂ := (LinearMap.proj ε).comp
        (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι 0)
      have hev := ev.toContinuousLinearMap.differentiable.comp_differentiableOn (hf.mono hVΩ)
      have hex : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ))) V :=
        (differentiable_id.mul_const _).cexp.differentiableOn
      apply (hex.mul hev).congr
      intro s hs
      exact (KPContFlatCuspIncomingEvaluation.sheetEvaluation_formula F ζ hζ C R P H U a ι s (f s) ε)
    exact L.differentiable.comp_differentiableOn hi
  apply ((L.differentiable.comp_differentiableOn he).sub hin).congr
  intro s hs
  have hsΩ := hVΩ hs
  change (coefficient F ζ hζ C R P H U a ι f s b).val 0 = _
  have hct := KPContinuation.ChamberOutgoingSource.actual_projected_upper_constantTerm_eq F ζ hζ C R P H U
    ι f hι hf s hs a 0 b
  rw [← KPContinuation.ChamberOutgoingSource.actual_projected_kernel_period_eq F ζ hζ C R P H U ι f hι hf s hs a 0 b] at hct
  simp only [KPIncomingCasimir.heightFactor, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at hct
  have hval := congrArg (fun v : ZeroFiber F ζ hζ C R P H U a => v.val 0) hct
  change L _ = _ + (coefficient F ζ hζ C R P H U a ι f s b).val 0 at hval
  have hinval : ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hsΩ (f s)).val b).val 0 =
      L (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s)) := rfl
  rw [hinval] at hval
  dsimp only [Pi.sub_apply, Function.comp_apply]
  change _ = L _ - L _
  linear_combination -hval

def zeroScalar (s : ℂ) (p : KPCuspCharts.Coordinates F) : ℂ :=
  (zeroMode F ζ hζ C R P H U a ι B f χ source s p.2 p.1.2).val 0

def parameterScalar (k : ℕ) (s : ℂ) (z : KPArch.Space (d F)) : ℂ :=
  iteratedDerivWithin k
    (fun w => zeroScalar F ζ hζ C R P H U a ι B f χ source w
      ((KPCuspCharts.toArchHomeomorph F
        (geometry F ζ hζ C R P H U a).positive_dimension).symm z)) V s

theorem parameterScalar_coordinates (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (p : KPCuspCharts.Coordinates F)
    (ht : T + 1 ≤ p.2) (hb : B.τ < p.2) :
    parameterScalar F ζ hζ C R P H U a ι B f χ source k s (KPCuspCharts.toArch F p) =
      iteratedDerivWithin k (fun w => KPChamberOutgoingL2.outgoingFactor (d F) w p.2 *
        (coefficient F ζ hζ C R P H U a ι f w 0).val 0) V s := by
  unfold parameterScalar
  change iteratedDerivWithin k
    (fun w => zeroScalar F ζ hζ C R P H U a ι B f χ source w
      ((KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension).symm
        ((KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension) p))) V s = _
  rw [Homeomorph.symm_apply_apply]
  apply iteratedDerivWithin_congr _ hs
  intro w hw
  change (zeroMode F ζ hζ C R P H U a ι B f χ source w p.2 p.1.2).val 0 = _
  rw [outgoing_formula F ζ hζ C R P H U a ι B f χ source hι hf w hw p.2 p.1.2 ht hb,
    coefficient_shape_constant F ζ hζ C R P H U a ι f w p.1.2 0]
  rfl

theorem coefficient_parameterJet_continuous (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (b : KPCuspCharts.Shape F) :
    ContinuousOn (iteratedDerivWithin k
      (fun s => (coefficient F ζ hζ C R P H U a ι f s b).val 0) V) V := by
  have h := (coefficient_holomorphic F ζ hζ C R P H U a ι f hι hf b).contDiffOn
    (n := (k : ℕ∞)) KPChamberL2Defect.chamber_isOpen
  exact h.continuousOn_iteratedDerivWithin (by simp) KPChamberL2Defect.chamber_isOpen.uniqueDiffOn

theorem outgoingFactor_parameter_deriv (n k : ℕ) (t : ℝ) (s : ℂ) (hs : s ∈ V) :
    iteratedDerivWithin k (fun w => KPChamberOutgoingL2.outgoingFactor n w t) V s =
      (-2 * (n : ℂ) * (t : ℂ)) ^ k * KPChamberOutgoingL2.outgoingFactor n s t := by
  let c : ℂ := -2 * (n : ℂ) * (t : ℂ)
  let a : ℂ := (n : ℂ) * (2 / 3 : ℂ) * (t : ℂ)
  have heq : (fun w => KPChamberOutgoingL2.outgoingFactor n w t) =
      fun w => Complex.exp a * Complex.exp (c * w) := by
    funext w
    rw [KPChamberOutgoingL2.outgoingFactor, ← Complex.exp_add]
    congr 1
    dsimp [a,c]
    ring
  rw [iteratedDerivWithin_eq_iteratedDeriv KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (by rw [heq]; fun_prop) hs, heq]
  rw [iteratedDeriv_const_mul _ (by fun_prop)]
  simp only [iteratedDeriv_cexp_const_mul]
  rw [congrFun heq s]
  dsimp [c]
  ring

theorem parameterScalar_expansion (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (p : KPCuspCharts.Coordinates F)
    (ht : T + 1 ≤ p.2) (hb : B.τ < p.2) :
    parameterScalar F ζ hζ C R P H U a ι B f χ source k s (KPCuspCharts.toArch F p) =
      KPChamberOutgoingL2.outgoingFactor (d F) s p.2 *
        ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) * (-2 * (d F : ℂ) * (p.2 : ℂ)) ^ i *
          iteratedDerivWithin (k-i) (fun w => (coefficient F ζ hζ C R P H U a ι f w 0).val 0) V s := by
  rw [parameterScalar_coordinates F ζ hζ C R P H U a ι B f χ source hι hf k s hs p ht hb]
  have hprod := iteratedDerivWithin_mul (n := k) hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (f := fun w => KPChamberOutgoingL2.outgoingFactor (d F) w p.2)
    (g := fun w => (coefficient F ζ hζ C R P H U a ι f w 0).val 0)
    (by unfold KPChamberOutgoingL2.outgoingFactor; fun_prop)
    (((coefficient_holomorphic F ζ hζ C R P H U a ι f hι hf 0).contDiffOn
      (n := (k : ℕ∞)) KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)
  rw [show (fun w => KPChamberOutgoingL2.outgoingFactor (d F) w p.2 *
      (coefficient F ζ hζ C R P H U a ι f w 0).val 0) =
    (fun w => KPChamberOutgoingL2.outgoingFactor (d F) w p.2) *
      (fun w => (coefficient F ζ hζ C R P H U a ι f w 0).val 0) from rfl, hprod]
  simp_rw [outgoingFactor_parameter_deriv _ _ _ _ hs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def radialPolynomial (k : ℕ) (s : ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (k+1), Polynomial.monomial i
    ((k.choose i : ℂ) * (-2 * (d F : ℂ))^i *
      iteratedDerivWithin (k-i) (fun w => (coefficient F ζ hζ C R P H U a ι f w 0).val 0) V s)

def radialModel (k : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (((d F : ℂ) * ((2/3 : ℂ)-2*s)) * (t : ℂ)) *
    (radialPolynomial F ζ hζ C R P H U a ι f k s).eval (t : ℂ)

theorem parameterScalar_radialModel (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (p : KPCuspCharts.Coordinates F)
    (ht : T+1 ≤ p.2) (hb : B.τ < p.2) :
    parameterScalar F ζ hζ C R P H U a ι B f χ source k s (KPCuspCharts.toArch F p) =
      radialModel F ζ hζ C R P H U a ι f k s p.2 := by
  rw [parameterScalar_expansion F ζ hζ C R P H U a ι B f χ source hι hf k s hs p ht hb]
  unfold radialModel radialPolynomial KPChamberOutgoingL2.outgoingFactor
  congr 1
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

theorem radialPolynomial_degree (k : ℕ) (s : ℂ) :
    (radialPolynomial F ζ hζ C R P H U a ι f k s).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  unfold radialPolynomial
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial]
  have him : i ≠ m := by have := Finset.mem_range.mp hi; omega
  simp [him]

def radialDerivativePolynomial (j k : ℕ) (s : ℂ) : Polynomial ℂ :=
  ((fun p : Polynomial ℂ => Polynomial.C ((d F : ℂ)*((2/3 : ℂ)-2*s))*p+p.derivative)^[j])
    (radialPolynomial F ζ hζ C R P H U a ι f k s)

theorem radialDerivativePolynomial_degree (j k : ℕ) (s : ℂ) :
    (radialDerivativePolynomial F ζ hζ C R P H U a ι f j k s).natDegree ≤ k := by
  induction j with
  | zero => exact radialPolynomial_degree F ζ hζ C R P H U a ι f k s
  | succ j ih =>
    unfold radialDerivativePolynomial at *
    rw [Function.iterate_succ_apply']
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ih
    · exact (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _) |>.trans ih

theorem radialDerivativePolynomial_coeff_continuous (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (j k m : ℕ) :
    ContinuousOn (fun s => (radialDerivativePolynomial F ζ hζ C R P H U a ι f j k s).coeff m) V := by
  induction j generalizing m with
  | zero =>
    change ContinuousOn (fun s => (radialPolynomial F ζ hζ C R P H U a ι f k s).coeff m) V
    unfold radialPolynomial
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    apply continuousOn_finset_sum
    intro i hi
    split_ifs
    · exact (coefficient_parameterJet_continuous F ζ hζ C R P H U a ι f hι hf (k-i) 0).const_mul _
    · exact continuousOn_const
  | succ j ih =>
    unfold radialDerivativePolynomial
    simp only [Function.iterate_succ_apply', Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative]
    exact ((by fun_prop : ContinuousOn (fun s : ℂ => (d F : ℂ)*((2/3 : ℂ)-2*s)) V).mul (ih m)).add
      ((ih (m+1)).mul_const _)

theorem polynomial_eval_bound (p : Polynomial ℂ) (k : ℕ) (hk : p.natDegree ≤ k)
    (c : ℝ) (hc : 0 ≤ c) (hcoeff : ∀ i ≤ k, ‖p.coeff i‖ ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    ‖p.eval (t : ℂ)‖ ≤ ((k+1 : ℕ) : ℝ)*c*(1+t)^k := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hk)]
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), ‖p.coeff i * (t : ℂ)^i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (k+1), c*(1+t)^k := by
      apply Finset.sum_le_sum
      intro i hi
      have hik := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
      apply mul_le_mul (hcoeff i hik) _ (pow_nonneg ht _) hc
      exact (pow_le_pow_left₀ ht (by linarith : t ≤ 1+t) i).trans
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1+t) hik)
    _ = _ := by simp [mul_assoc]

theorem radialDerivativePolynomial_compact_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (J k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K, ∀ j ≤ J, ∀ t : ℝ, 0 ≤ t →
      ‖(radialDerivativePolynomial F ζ hζ C R P H U a ι f j k s).eval (t : ℂ)‖ ≤ c*(1+t)^k := by
  let g : ℂ → (Cusps F ζ hζ C R P H U × Fin (J+1) × Fin (k+1) → ℂ) := fun s ai =>
    (radialDerivativePolynomial F ζ hζ C R P H U ai.1 ι f ai.2.1.val k s).coeff ai.2.2.val
  have hg : ContinuousOn g K := continuousOn_pi.mpr (fun ai =>
    (radialDerivativePolynomial_coeff_continuous F ζ hζ C R P H U ai.1 ι f hι hf ai.2.1.val k ai.2.2.val).mono hKV)
  obtain ⟨c,hc⟩ := hK.exists_bound_of_continuousOn hg
  refine ⟨((k+1 : ℕ) : ℝ)*max c 0, by positivity, ?_⟩
  intro a s hs j hj t ht
  apply polynomial_eval_bound _ k (radialDerivativePolynomial_degree F ζ hζ C R P H U a ι f j k s) (max c 0)
    (le_max_right _ _) _ t ht
  intro i hi
  exact (norm_le_pi_norm (g s) (a,⟨j,by omega⟩,⟨i,by omega⟩)).trans
    ((hc s hs).trans (le_max_left _ _))

theorem poly_radial_hasDeriv (q : ℂ) (p : Polynomial ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (q*(t : ℂ)) * p.eval (t : ℂ))
      (Complex.exp (q*(t : ℂ)) * (q*p.eval (t : ℂ) + p.derivative.eval (t : ℂ))) t := by
  have hp : HasDerivAt (fun t : ℝ => p.eval (t : ℂ)) (p.derivative.eval (t : ℂ)) t := by
    convert ((p.hasDerivAt (t : ℂ)).comp_ofReal) using 1 <;> simp
  have he : HasDerivAt (fun t : ℝ => Complex.exp (q*(t : ℂ)))
      (q*Complex.exp (q*(t : ℂ))) t := by
    have h := ((Complex.hasDerivAt_exp (q*(t : ℂ))).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul q)).comp_ofReal
    convert h using 1 <;> simp [mul_comm]

  convert he.mul hp using 1 <;> ring
theorem poly_radial_deriv (q : ℂ) (p : Polynomial ℂ) :
    deriv (fun t : ℝ => Complex.exp (q*(t : ℂ)) * p.eval (t : ℂ)) =
      fun t : ℝ => Complex.exp (q*(t : ℂ)) * (Polynomial.C q * p + p.derivative).eval (t : ℂ) := by
  funext t
  rw [(poly_radial_hasDeriv q p t).deriv]
  simp
theorem poly_radial_second (q : ℂ) (p : Polynomial ℂ) :
    deriv (deriv (fun t : ℝ => Complex.exp (q*(t : ℂ)) * p.eval (t : ℂ))) =
      fun t : ℝ => Complex.exp (q*(t : ℂ)) *
        (Polynomial.C q * (Polynomial.C q * p + p.derivative) + (Polynomial.C q * p + p.derivative).derivative).eval (t : ℂ) := by
  rw [poly_radial_deriv, poly_radial_deriv]

theorem radialModel_derivatives (k : ℕ) (s : ℂ) :
    let q : ℂ := (d F : ℂ)*((2/3 : ℂ)-2*s)
    let p := radialPolynomial F ζ hζ C R P H U a ι f k s
    Differentiable ℝ (radialModel F ζ hζ C R P H U a ι f k s) ∧
    Differentiable ℝ (deriv (radialModel F ζ hζ C R P H U a ι f k s)) ∧
    (∀ t : ℝ, deriv (radialModel F ζ hζ C R P H U a ι f k s) t =
      Complex.exp (q*(t : ℂ)) * (Polynomial.C q*p+p.derivative).eval (t : ℂ)) ∧
    (∀ t : ℝ, deriv (deriv (radialModel F ζ hζ C R P H U a ι f k s)) t =
      Complex.exp (q*(t : ℂ)) *
        (Polynomial.C q*(Polynomial.C q*p+p.derivative)+(Polynomial.C q*p+p.derivative).derivative).eval (t : ℂ)) := by
  dsimp only
  unfold radialModel
  refine ⟨fun t => (poly_radial_hasDeriv _ _ t).differentiableAt, ?_, ?_, ?_⟩
  · rw [poly_radial_deriv]
    exact fun t => (poly_radial_hasDeriv _ _ t).differentiableAt
  · intro t; rw [poly_radial_deriv]
  · intro t; rw [poly_radial_second]

def frameDerivative (n : ℕ) (v : Fin n × Fin 3) (g : KPArch.Space n → ℂ)
    (z : KPArch.Space n) : ℂ :=
  let q : Fin 3 := if v.2 = 0 then 2 else if v.2 = 1 then 0 else 1
  let weight : ℝ := if v.2 = 0 then 1 else KPArch.height (z v.1)
  (weight : ℂ) * fderiv ℝ g z
    (KPContActualSphericalFlatStage.coordinateDirection n v.1 q)

def hessian (n : ℕ) (g : KPArch.Space n → ℂ) (z : KPArch.Space n)
    (v w : Fin n × Fin 3) : ℂ :=
  frameDerivative n v (fun y => frameDerivative n w g y) z -
    (if v.1 = w.1 ∧ v.2 ≠ 0 ∧ w.2 = v.2 then
      frameDerivative n (v.1, 0) g z else 0) +
    (if v.1 = w.1 ∧ v.2 ≠ 0 ∧ w.2 = 0 then frameDerivative n v g z else 0)

theorem meanHeight_fderiv (n : ℕ) (z u : KPArch.Space n) :
    fderiv ℝ (KPCuspLogShape.meanHeight n) z u = (n : ℝ)⁻¹ * ∑ i, (u i).2 := by
  have h : HasFDerivAt (KPCuspLogShape.meanHeight n)
      ((n : ℝ)⁻¹ • ∑ i : Fin n, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj i)) z := by
    have heq : KPCuspLogShape.meanHeight n = fun y : KPArch.Space n => (n : ℝ)⁻¹ * ∑ i, (y i).2 := by
      funext y; simp only [KPCuspLogShape.meanHeight]; ring
    rw [heq]
    have hS : HasFDerivAt (fun y : KPArch.Space n => ∑ i, (y i).2)
        (∑ i : Fin n, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj i)) z := by fun_prop
    exact hS.const_mul _
  rw [h.fderiv]
  simp
theorem meanHeight_differentiable (n : ℕ) : Differentiable ℝ (KPCuspLogShape.meanHeight n) := by
  unfold KPCuspLogShape.meanHeight
  fun_prop

theorem frameDerivative_radial (n : ℕ) (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (z : KPArch.Space n) (v : Fin n × Fin 3) :
    frameDerivative n v (fun y => g (KPCuspLogShape.meanHeight n y)) z =
      if v.2 = 0 then (n : ℂ)⁻¹ * deriv g (KPCuspLogShape.meanHeight n z) else 0 := by
  unfold frameDerivative
  dsimp only
  change _ * fderiv ℝ (g ∘ KPCuspLogShape.meanHeight n) z _ = _
  rw [fderiv_comp z (hg _) (meanHeight_differentiable n z)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv, meanHeight_fderiv]
  simp only [Algebra.smul_def]
  have hdir (q : Fin 3) : ∑ i, (KPContActualSphericalFlatStage.coordinateDirection n v.1 q i).2 =
      if q = 2 then 1 else 0 := by
    rw [Finset.sum_eq_single v.1]
    · fin_cases q <;> simp [KPContActualSphericalFlatStage.coordinateDirection]
    · intro i hi hne
      simp [KPContActualSphericalFlatStage.coordinateDirection, Pi.single_eq_of_ne hne]
    · simp
  rw [hdir]
  by_cases hv : v.2 = 0
  · simp [hv]
  · by_cases hv1 : v.2 = 1 <;> simp [hv, hv1]

theorem hessian_radial (n : ℕ) (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) (z : KPArch.Space n) (v w : Fin n × Fin 3) :
    hessian n (fun y => g (KPCuspLogShape.meanHeight n y)) z v w =
      (if v.2 = 0 ∧ w.2 = 0 then (n : ℂ)⁻¹ ^ 2 * deriv (deriv g) (KPCuspLogShape.meanHeight n z) else 0) -
      (if v.1 = w.1 ∧ v.2 ≠ 0 ∧ w.2 = v.2 then (n : ℂ)⁻¹ * deriv g (KPCuspLogShape.meanHeight n z) else 0) := by
  unfold hessian
  simp_rw [frameDerivative_radial n g hg]
  by_cases hw : w.2 = 0
  · simp only [hw, ite_true]
    have heq : (fun y => (n : ℂ)⁻¹ * deriv g (KPCuspLogShape.meanHeight n y)) =
        fun y => ((fun t => (n : ℂ)⁻¹ * deriv g t) (KPCuspLogShape.meanHeight n y)) := rfl
    rw [heq, frameDerivative_radial n _ ((hg').const_mul _)]
    simp_rw [deriv_const_mul _ (hg' _)]
    by_cases hv : v.2 = 0 <;> simp [hv, hw, pow_two, mul_assoc]
  · simp only [hw, ite_false]
    have hz : frameDerivative n v (fun _ : KPArch.Space n => (0 : ℂ)) z = 0 := by
      simp [frameDerivative]
    rw [hz]
    by_cases hv : v.2 = 0 <;> simp [hv, hw]

theorem parameterScalar_radialModel_germ (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (z : KPArch.Space (d F))
    (ht : T+1 < KPCuspLogShape.meanHeight (d F) z)
    (hb : B.τ < KPCuspLogShape.meanHeight (d F) z) :
    parameterScalar F ζ hζ C R P H U a ι B f χ source k s =ᶠ[𝓝 z]
      (fun y => radialModel F ζ hζ C R P H U a ι f k s (KPCuspLogShape.meanHeight (d F) y)) := by
  have hcont : Continuous (KPCuspLogShape.meanHeight (d F)) := (meanHeight_differentiable (d F)).continuous
  have hnhds : {y : KPArch.Space (d F) | T+1 < KPCuspLogShape.meanHeight (d F) y ∧
      B.τ < KPCuspLogShape.meanHeight (d F) y} ∈ 𝓝 z :=
    (IsOpen.inter (isOpen_lt continuous_const hcont) (isOpen_lt continuous_const hcont)).mem_nhds ⟨ht,hb⟩
  filter_upwards [hnhds] with y hy
  let h := KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension
  let p := h.symm y
  have hp : KPCuspCharts.toArch F p = y := h.apply_symm_apply y
  have hmean : p.2 = KPCuspLogShape.meanHeight (d F) y := by
    rw [← hp, KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension]
  rw [← hp]
  rw [parameterScalar_radialModel F ζ hζ C R P H U a ι B f χ source hι hf k s hs p
    (by rw [hmean]; exact hy.1.le) (by rw [hmean]; exact hy.2),
    KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension]

def covariantNorm (n : ℕ) (j : Fin 3) (g : KPArch.Space n → ℂ)
    (z : KPArch.Space n) : ℝ :=
  if j = 0 then ‖g z‖ else if j = 1 then
    Real.sqrt (∑ v : Fin n × Fin 3, ‖frameDerivative n v g z‖ ^ 2)
  else Real.sqrt (∑ v : Fin n × Fin 3, ∑ w : Fin n × Fin 3, ‖hessian n g z v w‖ ^ 2)

theorem sqrt_sum_norm_bound {I : Type*} [Fintype I]
    (u : I → ℂ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ i, ‖u i‖ ≤ B) :
    Real.sqrt (∑ i, ‖u i‖^2) ≤ (Fintype.card I + 1 : ℝ)*B := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs : (∑ i, ‖u i‖^2) ≤ (Fintype.card I : ℝ)*B^2 := by
    calc
      _ ≤ ∑ _ : I, B^2 := Finset.sum_le_sum (fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hu i) _)
      _ = _ := by simp
  have hN : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg B, sq_nonneg ((Fintype.card I : ℝ)*B)]

theorem covariantNorm_radial_bound (n : ℕ) (hn : 0 < n) (j : Fin 3)
    (g : ℝ → ℂ) (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (z : KPArch.Space n) (B : ℝ) (hB : 0 ≤ B)
    (h0 : ‖g (KPCuspLogShape.meanHeight n z)‖ ≤ B)
    (h1 : ‖deriv g (KPCuspLogShape.meanHeight n z)‖ ≤ B)
    (h2 : ‖deriv (deriv g) (KPCuspLogShape.meanHeight n z)‖ ≤ B) :
    covariantNorm n j (fun y => g (KPCuspLogShape.meanHeight n y)) z ≤
      (2*((3*n : ℕ)^2+1) : ℝ)*B := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : ‖(n : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hnR
  have hframe : ∀ v, ‖frameDerivative n v (fun y => g (KPCuspLogShape.meanHeight n y)) z‖ ≤ B := by
    intro v
    rw [frameDerivative_radial n g hg]
    split_ifs
    · rw [norm_mul]
      exact (mul_le_mul hinv h1 (norm_nonneg _) (by positivity)).trans_eq (one_mul B)
    · simpa using hB
  have hhess : ∀ v w, ‖hessian n (fun y => g (KPCuspLogShape.meanHeight n y)) z v w‖ ≤ 2*B := by
    intro v w
    rw [hessian_radial n g hg hg']
    apply (norm_sub_le _ _).trans
    have ha : ‖if v.2 = 0 ∧ w.2 = 0 then (n : ℂ)⁻¹^2 * deriv (deriv g) (KPCuspLogShape.meanHeight n z) else 0‖ ≤ B := by
      split_ifs
      · rw [norm_mul, norm_pow]
        exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinv _) h2 (norm_nonneg _) (by positivity)).trans_eq (by simp)
      · simpa using hB
    have hb : ‖if v.1 = w.1 ∧ v.2 ≠ 0 ∧ w.2 = v.2 then (n : ℂ)⁻¹ * deriv g (KPCuspLogShape.meanHeight n z) else 0‖ ≤ B := by
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul hinv h1 (norm_nonneg _) (by positivity)).trans_eq (one_mul B)
      · simpa using hB
    linarith
  unfold covariantNorm
  split_ifs with hj0 hj1
  · have hM : 1 ≤ (2*((3*n : ℕ)^2+1) : ℝ) := by norm_cast; omega
    exact h0.trans (le_mul_of_one_le_left hB hM)
  · have hs := sqrt_sum_norm_bound _ B hB hframe
    have hM : (Fintype.card (Fin n × Fin 3) + 1 : ℝ) ≤ (2*((3*n : ℕ)^2+1) : ℝ) := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      push_cast
      nlinarith [sq_nonneg (3*(n : ℝ)-1)]
    exact hs.trans (mul_le_mul_of_nonneg_right hM hB)
  · have hs := sqrt_sum_norm_bound (fun vw : (Fin n × Fin 3) × (Fin n × Fin 3) =>
        hessian n (fun y => g (KPCuspLogShape.meanHeight n y)) z vw.1 vw.2) (2*B) (by positivity)
        (fun vw => hhess vw.1 vw.2)
    rw [Fintype.sum_prod_type] at hs
    convert hs using 1 <;> simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] <;> ring

def jetNorm (k : ℕ) (j : Fin 3) (s : ℂ) (p : KPCuspCharts.Coordinates F) : ℝ :=
  covariantNorm (d F) j
    (parameterScalar F ζ hζ C R P H U a ι B f χ source k s) (KPCuspCharts.toArch F p)

theorem frameDerivative_congr_germ (n : ℕ) (f g : KPArch.Space n → ℂ)
    (z : KPArch.Space n) (h : f =ᶠ[𝓝 z] g) (v : Fin n × Fin 3) :
    frameDerivative n v f =ᶠ[𝓝 z] frameDerivative n v g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  unfold frameDerivative
  rw [hy]

theorem covariantNorm_congr_germ (n : ℕ) (j : Fin 3) (f g : KPArch.Space n → ℂ)
    (z : KPArch.Space n) (h : f =ᶠ[𝓝 z] g) : covariantNorm n j f z = covariantNorm n j g z := by
  have hf (v : Fin n × Fin 3) := frameDerivative_congr_germ n f g z h v
  have hh (v w : Fin n × Fin 3) : hessian n f z v w = hessian n g z v w := by
    unfold hessian
    rw [(frameDerivative_congr_germ n (frameDerivative n w f) (frameDerivative n w g) z (hf w) v).eq_of_nhds,
      (hf (v.1,0)).eq_of_nhds, (hf v).eq_of_nhds]
  unfold covariantNorm
  simp only [h.eq_of_nhds, fun v => (hf v).eq_of_nhds, hh]

theorem jetNorm_radialModel (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (j : Fin 3) (s : ℂ) (hs : s ∈ V) (p : KPCuspCharts.Coordinates F)
    (ht : T+1 < p.2) (hb : B.τ < p.2) :
    jetNorm F ζ hζ C R P H U a ι B f χ source k j s p =
      covariantNorm (d F) j (fun y => radialModel F ζ hζ C R P H U a ι f k s
        (KPCuspLogShape.meanHeight (d F) y)) (KPCuspCharts.toArch F p) := by
  unfold jetNorm
  apply covariantNorm_congr_germ
  apply parameterScalar_radialModel_germ F ζ hζ C R P H U a ι B f χ source hι hf k s hs
  · rwa [KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension]
  · rwa [KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension]

theorem radialModel_compact_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K, ∀ t : ℝ, 0 ≤ t →
      ‖radialModel F ζ hζ C R P H U a ι f k s t‖ ≤ c*(1+t)^k*‖KPChamberOutgoingL2.outgoingFactor (d F) s t‖ ∧
      ‖deriv (radialModel F ζ hζ C R P H U a ι f k s) t‖ ≤ c*(1+t)^k*‖KPChamberOutgoingL2.outgoingFactor (d F) s t‖ ∧
      ‖deriv (deriv (radialModel F ζ hζ C R P H U a ι f k s)) t‖ ≤ c*(1+t)^k*‖KPChamberOutgoingL2.outgoingFactor (d F) s t‖ := by
  obtain ⟨c,hc,hbound⟩ := radialDerivativePolynomial_compact_bound F ζ hζ C R P H U ι f hι hf K hK hKV 2 k
  refine ⟨c,hc,?_⟩
  intro a s hs t ht
  have hd := radialModel_derivatives F ζ hζ C R P H U a ι f k s
  dsimp only at hd
  constructor
  · unfold radialModel
    rw [norm_mul, mul_comm (c*(1+t)^k)]
    exact mul_le_mul_of_nonneg_left (hbound a s hs 0 (by omega) t ht) (norm_nonneg _)
  constructor
  · rw [hd.2.2.1 t, norm_mul, mul_comm (c*(1+t)^k)]
    exact mul_le_mul_of_nonneg_left (hbound a s hs 1 (by omega) t ht) (norm_nonneg _)
  · rw [hd.2.2.2 t, norm_mul, mul_comm (c*(1+t)^k)]
    exact mul_le_mul_of_nonneg_left (hbound a s hs 2 (by omega) t ht) (norm_nonneg _)

theorem uniform_covariant_jets (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) (j : Fin 3) :
    ∃ t₀ c : ℝ, 0 ≤ t₀ ∧ T+1 < t₀ ∧ B.τ < t₀ ∧ 0 ≤ c ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K, ∀ p : KPCuspCharts.Coordinates F, t₀ ≤ p.2 →
        Real.exp (-(d F : ℝ)*p.2)*jetNorm F ζ hζ C R P H U a ι B f χ source k j s p ≤
          c*(1+p.2)^k*Real.exp (-(d F : ℝ)*p.2) := by
  obtain ⟨c,hc,hbound⟩ := radialModel_compact_bound F ζ hζ C R P H U ι f hι hf K hK hKV k
  let M : ℝ := (2*((3*d F : ℕ)^2+1) : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let t₀ : ℝ := max 0 (max (T+1) B.τ)+1
  have ht0 : 0 ≤ t₀ := by dsimp [t₀]; have := le_max_left 0 (max (T+1) B.τ); linarith
  have hT : T+1 < t₀ := by dsimp [t₀]; have := le_max_left (T+1) B.τ; have := le_max_right 0 (max (T+1) B.τ); linarith
  have hB : B.τ < t₀ := by dsimp [t₀]; have := le_max_right (T+1) B.τ; have := le_max_right 0 (max (T+1) B.τ); linarith
  refine ⟨t₀,M*c,ht0,hT,hB,mul_nonneg hM hc,?_⟩
  intro a s hs p hp
  have ht : 0 ≤ p.2 := ht0.trans hp
  have hd := radialModel_derivatives F ζ hζ C R P H U a ι f k s
  dsimp only at hd
  obtain ⟨h0,h1,h2⟩ := hbound a s hs p.2 ht
  have hn := covariantNorm_radial_bound (d F) (geometry F ζ hζ C R P H U a).positive_dimension j
    _ hd.1 hd.2.1 (KPCuspCharts.toArch F p)
    (c*(1+p.2)^k*‖KPChamberOutgoingL2.outgoingFactor (d F) s p.2‖) (by positivity)
    (by rwa [KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension])
    (by rwa [KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension])
    (by rwa [KPCuspCharts.toArch_meanHeight F (geometry F ζ hζ C R P H U a).positive_dimension])
  rw [jetNorm_radialModel F ζ hζ C R P H U a ι B f χ source hι hf k j s (hKV hs) p (by linarith) (by linarith)]
  calc
    _ ≤ Real.exp (-(d F : ℝ)*p.2)*(M*(c*(1+p.2)^k*‖KPChamberOutgoingL2.outgoingFactor (d F) s p.2‖)) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = ((M*c)*(1+p.2)^k)*(Real.exp (-(d F : ℝ)*p.2)*‖KPChamberOutgoingL2.outgoingFactor (d F) s p.2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_margin F s (hKV hs) p.2 ht) (by positivity)

theorem radial_covariantNorm_continuous (n : ℕ) (j : Fin 3) (q : ℂ) (p : Polynomial ℂ) :
    Continuous (fun z : KPArch.Space n => covariantNorm n j
      (fun y => Complex.exp (q*(KPCuspLogShape.meanHeight n y : ℂ))*p.eval (KPCuspLogShape.meanHeight n y : ℂ)) z) := by
  let g : ℝ → ℂ := fun t => Complex.exp (q*(t : ℂ))*p.eval (t : ℂ)
  have hg : Differentiable ℝ g := fun t => (poly_radial_hasDeriv q p t).differentiableAt
  have hg' : Differentiable ℝ (deriv g) := by
    dsimp only [g]
    rw [poly_radial_deriv]
    exact fun t => (poly_radial_hasDeriv _ _ t).differentiableAt
  have hc : Continuous (KPCuspLogShape.meanHeight n) := (meanHeight_differentiable n).continuous
  have hc0 : Continuous (fun z => g (KPCuspLogShape.meanHeight n z)) := hg.continuous.comp hc
  have hc1 : Continuous (fun z => deriv g (KPCuspLogShape.meanHeight n z)) := hg'.continuous.comp hc
  have hc2 : Continuous (fun z => deriv (deriv g) (KPCuspLogShape.meanHeight n z)) := by
    dsimp only [g]
    rw [poly_radial_second]
    have hdiff : Differentiable ℝ (fun t : ℝ => Complex.exp (q*(t : ℂ)) *
        (Polynomial.C q*(Polynomial.C q*p+p.derivative)+(Polynomial.C q*p+p.derivative).derivative).eval (t : ℂ)) :=
      fun t => (poly_radial_hasDeriv q _ t).differentiableAt
    exact hdiff.continuous.comp hc
  change Continuous (fun z => covariantNorm n j (fun y => g (KPCuspLogShape.meanHeight n y)) z)
  unfold covariantNorm
  split_ifs
  · exact hc0.norm
  · simp_rw [frameDerivative_radial n g hg]
    apply Continuous.sqrt
    apply continuous_finset_sum
    intro v hv
    split_ifs <;> fun_prop
  · simp_rw [hessian_radial n g hg hg']
    apply Continuous.sqrt
    apply continuous_finset_sum
    intro v hv
    apply continuous_finset_sum
    intro w hw
    split_ifs <;> fun_prop

theorem jetNorm_high_aestronglyMeasurable (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (j : Fin 3) (s : ℂ) (hs : s ∈ V) (A : ℝ) (hT : T+1 < A) (hB : B.τ < A) :
    AEStronglyMeasurable (jetNorm F ζ hζ C R P H U a ι B f χ source k j s)
      ((endMeasure F ζ hζ C R P H U a).restrict (tail F A)) := by
  let model : KPCuspCharts.Coordinates F → ℝ := fun p => covariantNorm (d F) j
    (fun y => radialModel F ζ hζ C R P H U a ι f k s (KPCuspLogShape.meanHeight (d F) y))
    (KPCuspCharts.toArch F p)
  have hm : Continuous model := by
    exact (radial_covariantNorm_continuous _ _ _ _).comp (KPCuspCharts.toArch_contDiff F).continuous
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (by exact measurableSet_Ioi.preimage measurable_snd : MeasurableSet (tail F A))] with p hp
  exact (jetNorm_radialModel F ζ hζ C R P H U a ι B f χ source hι hf k j s hs p
    (by change A < p.2 at hp; linarith) (by change A < p.2 at hp; linarith)).symm

theorem polynomial_square_exp_bound (k : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → (1+t)^(2*k) ≤ M*Real.exp (r*t) := by
  let M : ℝ := ((2*k).factorial : ℝ)*r⁻¹^(2*k)*Real.exp r
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro t ht
  have hx : 0 ≤ r*(1+t) := by positivity
  have h := (Real.pow_div_factorial_le_exp (r*(1+t)) hx (2*k))
  have hf : 0 < ((2*k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hrpow : 0 < r^(2*k) := pow_pos hr _
  rw [div_le_iff₀ hf, mul_pow] at h
  have hp : r⁻¹^(2*k)*r^(2*k) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  calc
    _ = r⁻¹^(2*k)*(r^(2*k)*(1+t)^(2*k)) := by rw [← mul_assoc, hp, one_mul]
    _ ≤ r⁻¹^(2*k)*(Real.exp (r*(1+t))*((2*k).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = M*Real.exp (r*t) := by
      rw [show r*(1+t) = r+r*t by ring, Real.exp_add]
      dsimp [M]
      ring

set_option maxHeartbeats 1200000 in

theorem square_jet_exponential_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) (j : Fin 3) :
    ∃ t₀ M : ℝ, 0 ≤ t₀ ∧ T+1 < t₀ ∧ B.τ < t₀ ∧ 0 ≤ M ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K, ∀ p : KPCuspCharts.Coordinates F, t₀ ≤ p.2 →
        jetNorm F ζ hζ C R P H U a ι B f χ source k j s p ^ 2 ≤ M*Real.exp ((d F : ℝ)*p.2) := by
  obtain ⟨t₀,c,h0,hT,hB,hc,hbound⟩ := uniform_covariant_jets F ζ hζ C R P H U ι B f χ source hι hf K hK hKV k j
  have hd : 0 < (d F : ℝ) := by exact_mod_cast KPCuspLogShape.dimension_pos F H.totallyComplex
  obtain ⟨M,hM,hpoly⟩ := polynomial_square_exp_bound k (d F : ℝ) hd
  refine ⟨t₀,c^2*M,h0,hT,hB,by positivity,?_⟩
  intro a s hs p hp
  have hn := hbound a s hs p hp
  have hnon : 0 ≤ jetNorm F ζ hζ C R P H U a ι B f χ source k j s p := by
    unfold jetNorm covariantNorm
    split_ifs <;> positivity
  have hu : jetNorm F ζ hζ C R P H U a ι B f χ source k j s p ≤ c*(1+p.2)^k :=
    (mul_le_mul_iff_left₀ (Real.exp_pos (-(d F : ℝ)*p.2))).mp (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hn)
  calc
    _ ≤ (c*(1+p.2)^k)^2 := pow_le_pow_left₀ hnon hu 2
    _ = c^2*(1+p.2)^(2*k) := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ c^2*(M*Real.exp ((d F : ℝ)*p.2)) := mul_le_mul_of_nonneg_left (hpoly p.2 (h0.trans hp)) (sq_nonneg _)
    _ = _ := by ring

def squareTail (k : ℕ) (j : Fin 3) (s : ℂ) (A : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in tail F A,
    ENNReal.ofReal (jetNorm F ζ hζ C R P H U a ι B f χ source k j s p ^ 2)
    ∂endMeasure F ζ hζ C R P H U a

set_option maxHeartbeats 1500000 in

theorem jets_memLp_square_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) (j : Fin 3) :
    ∃ t₀ M : ℝ, 0 ≤ t₀ ∧ T+1 < t₀ ∧ B.τ < t₀ ∧ 0 ≤ M ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K,
        MemLp (jetNorm F ζ hζ C R P H U a ι B f χ source k j s) 2
          ((endMeasure F ζ hζ C R P H U a).restrict (tail F t₀)) ∧
        squareTail F ζ hζ C R P H U a ι B f χ source k j s t₀ ≤ ENNReal.ofReal M := by
  obtain ⟨t₀,M,h0,hT,hB,hM,hbound⟩ := square_jet_exponential_bound F ζ hζ C R P H U ι B f χ source hι hf K hK hKV k j
  let mass : Cusps F ζ hζ C R P H U → ℝ≥0∞ := fun a => M.toNNReal •
    (∫⁻ p in tail F t₀, ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U a)
  have hfin (a : Cusps F ζ hζ C R P H U) : mass a < ⊤ := by
    exact ENNReal.mul_lt_top (by simp) (end_exponential_mass_finite F ζ hζ C R P H U a (d F : ℝ)
      (by
        have hd : 0 < (d F : ℝ) := by exact_mod_cast KPCuspLogShape.dimension_pos F H.totallyComplex
        linarith) t₀)
  have hmass : ∀ a, mass a ≤ ENNReal.ofReal ((mass a).toReal) := fun a => by rw [ENNReal.ofReal_toReal (hfin a).ne]
  let N : ℝ := ∑ a : Cusps F ζ hζ C R P H U, (mass a).toReal
  have hN : 0 ≤ N := Finset.sum_nonneg (fun a ha => ENNReal.toReal_nonneg)
  refine ⟨t₀,N,h0,hT,hB,hN,?_⟩
  intro a s hs
  have hm := jetNorm_high_aestronglyMeasurable F ζ hζ C R P H U a ι B f χ source hι hf k j s (hKV hs) t₀ hT hB
  have hjpos (p) : 0 ≤ jetNorm F ζ hζ C R P H U a ι B f χ source k j s p := by
    unfold jetNorm covariantNorm; split_ifs <;> positivity
  have hsq : squareTail F ζ hζ C R P H U a ι B f χ source k j s t₀ ≤ mass a := by
    unfold squareTail mass
    change (∫⁻ p in tail F t₀, ENNReal.ofReal (jetNorm F ζ hζ C R P H U a ι B f χ source k j s p ^ 2) ∂_) ≤
      ENNReal.ofReal M * (∫⁻ p in tail F t₀, ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂_)
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (by exact measurableSet_Ioi.preimage measurable_snd : MeasurableSet (tail F t₀))] with p hp
    rw [← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_ofReal (hbound a s hs p (by exact (show t₀ < p.2 from hp).le))
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).mpr
    refine ⟨hm.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [squareTail, Real.norm_eq_abs, abs_of_nonneg (hjpos _), abs_pow] using hsq.trans_lt (hfin a)
  · apply hsq.trans
    apply (hmass a).trans
    apply ENNReal.ofReal_le_ofReal
    exact Finset.single_le_sum (fun b hb => ENNReal.toReal_nonneg) (Finset.mem_univ a)

theorem exponential_tail_tendsto (A₀ : ℝ) :
    Filter.Tendsto (fun A : ℝ => ∫⁻ p in tail F A,
      ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U a)
      Filter.atTop (𝓝 0) := by
  let ν := (endMeasure F ζ hζ C R P H U a).withDensity
    (fun p => ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)))
  have hmeas (A : ℝ) : MeasurableSet (tail F A) := measurableSet_Ioi.preimage measurable_snd
  have hanti : Antitone (tail F) := by
    intro A B hAB p hp
    exact lt_of_le_of_lt hAB hp
  have hinter : (⋂ A : ℝ, tail F A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := Set.mem_iInter.mp hp (p.2+1)
    change p.2+1 < p.2 at h
    linarith
  have hfin : ν (tail F A₀) ≠ ⊤ := by
    rw [withDensity_apply _ (hmeas A₀)]
    exact (end_exponential_mass_finite F ζ hζ C R P H U a (d F : ℝ)
      (by
        have hd : 0 < (d F : ℝ) := by exact_mod_cast KPCuspLogShape.dimension_pos F H.totallyComplex
        linarith) A₀).ne
  have h := tendsto_measure_iInter_atTop (μ := ν) (fun A => (hmeas A).nullMeasurableSet) hanti ⟨A₀,hfin⟩
  simp only [hinter, measure_empty, Function.comp_apply] at h
  have heq : (⇑ν ∘ tail F) = (fun A : ℝ => ∫⁻ p in tail F A,
      ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U a) := by
    funext A
    exact withDensity_apply _ (hmeas A)
  rwa [heq] at h

theorem squareTail_uniform_vanishing (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) (j : Fin 3) (t₀ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, t₀ ≤ A ∧ ∀ A' : ℝ, A ≤ A' →
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K,
        squareTail F ζ hζ C R P H U a ι B f χ source k j s A' ≤ ENNReal.ofReal ε := by
  obtain ⟨τ,M,hτ,hT,hB,hM,hbound⟩ := square_jet_exponential_bound F ζ hζ C R P H U ι B f χ source hι hf K hK hKV k j
  let mass : ℝ → ℝ≥0∞ := fun A => ENNReal.ofReal M *
    ∑ a : Cusps F ζ hζ C R P H U,
      ∫⁻ p in tail F A, ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U a
  have hsum : Filter.Tendsto (fun A : ℝ => ∑ a : Cusps F ζ hζ C R P H U,
      ∫⁻ p in tail F A, ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U a)
      Filter.atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun a ha => exponential_tail_tendsto F ζ hζ C R P H U a τ)
  have hmass : Filter.Tendsto mass Filter.atTop (𝓝 0) := by
    simpa [mass] using ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.ofReal_ne_top)
  intro ε hε
  have hsmall := hmass.eventually_le_const (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max t₀ (max τ A), le_max_left _ _, ?_⟩
  intro A' hA' a s hs
  have hτA : τ ≤ A' := (le_max_left τ A).trans ((le_max_right t₀ (max τ A)).trans hA')
  have hAA : A ≤ A' := (le_max_right τ A).trans ((le_max_right t₀ (max τ A)).trans hA')
  apply le_trans _ (hA A' hAA)
  unfold squareTail mass
  calc
    _ ≤ ENNReal.ofReal M * (∫⁻ p in tail F A', ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2))
        ∂endMeasure F ζ hζ C R P H U a) := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by exact measurableSet_Ioi.preimage measurable_snd : MeasurableSet (tail F A'))] with p hp
      rw [← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (hbound a s hs p (hτA.trans (show A' < p.2 from hp).le))
    _ ≤ _ := by
      apply mul_le_mul_right
      exact Finset.single_le_sum (f := fun b : Cusps F ζ hζ C R P H U =>
        ∫⁻ p in tail F A', ENNReal.ofReal (Real.exp ((d F : ℝ)*p.2)) ∂endMeasure F ζ hζ C R P H U b)
        (fun b hb => zero_le) (Finset.mem_univ a)

end DedekindZetaZeroFree.KPContActualChamberOutgoingAdapter

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
