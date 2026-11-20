module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Probes.Poisson.TwistedRows
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyIdentification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawInitialKernel31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

section

variable (u : Frequency D.recipe)

def rawInitialIntegrand (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  RawFixed.FixedData.rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
    ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I) ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I) Z

def rawinitialRowIntegral (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rawInitialIntegrand D u Z t

theorem separatedSeries_eq_rawFactor (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries D.recipe u ξ w z = RawFixed.FixedData.rawFactor D u ξ w z := by
  let P := RawFixed.FixedData.pkg D
  have h : RawFrequencyPublicBridge.Bridge D P.U P.P P.M P.plus P.minus :=
    { raw_u := P.U_u
      finite := P.deletion_finite
      plus_coeff := P.plus_mask
      minus_coeff := P.minus_mask
      plus_nonprincipal := fun v hv => (P.nonprincipal v hv).1
      minus_nonprincipal := fun v hv => (P.nonprincipal v hv).2
      plus_diff := fun v hv => P.plus_diff v (P.nonprincipal v hv).1
      minus_diff := fun v hv => P.minus_diff v (P.nonprincipal v hv).2
      plus_series := P.plus_eq
      minus_series := P.minus_eq }
  exact RawFrequencyPublicBridge.Bridge.quotient_right_eq h u ξ w z hξ hw hz

end

abbrev AIdx : Type :=
  ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior × D.recipe.A.Exterior ×
    D.recipe.A.Exterior

private theorem exterior_countable' : Countable D.recipe.A.Exterior := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have he := (DedekindZetaZeroFree.ProbeExteriorIdealCount.ideal_norm_summable F
    D.recipe.A.cS 2 (by norm_num)).countable_support
  have hall : Function.support (fun I : D.recipe.A.Exterior => (idealNorm I.val) ^ (-(2 : ℝ))) =
      Set.univ := by
    ext I
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (D.recipe.A.exteriorNorm_pos I) _).ne'
  rw [hall] at he
  exact Set.countable_univ_iff.mp he

private theorem aIndex_countable' : Countable (AIdx D) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI := exterior_countable' D
  letI : Countable (ExteriorSquarefreeIdeal D.recipe.A.cS) := by
    change Countable {I : D.recipe.A.Exterior // Squarefree I.val}
    infer_instance
  infer_instance

private alias integral_three' := DedekindZetaZeroFree.Quantitative.PoissonFrequencyDecomposition.FrequencyDecomposition.integral_three''

theorem frequencyNorm_pos' (u : Frequency D.recipe) : 0 < frequencyNorm D.recipe u := by
  rw [← RawFixed.FixedData.rawFrequency_norm D u]
  exact_mod_cast D.recipe.A.exteriorNorm_pos _

section

variable (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z)

include hZ in
theorem rawKernel_eq_tsum (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    RawFixed.FixedData.rawKernel D u ξ w z Z =
      ∑' a : AIdx D, NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z)
        Z ξ w z * NormalizedProbe.weightedSeparatedSummand D.recipe.probe (u, a) ξ w z := by
  rw [tsum_mul_left]
  have hs : ∑' a : AIdx D, NormalizedProbe.weightedSeparatedSummand D.recipe.probe (u, a) ξ w z =
      comparisonRealPower (frequencyNorm D.recipe u) (-z) * separatedSeries D.recipe u ξ w z := by
    simp only [NormalizedProbe.weightedSeparatedSummand, tsum_mul_left]
    rfl
  rw [hs, PoissonInitialBridge.tripleMellinWeight_eq D Z hZ ξ w z]
  unfold RawFixed.FixedData.rawKernel
  rw [← separatedSeries_eq_rawFactor D u ξ w z hξ hw hz,
    PoissonInitialBridge.cpow_eq_comparisonRealPower (frequencyNorm_pos' D u)]
  ring

include hZ in
theorem rawInitialIntegrand_eq_twisted
    (t : ℝ × ℝ × ℝ) :
    rawInitialIntegrand D u Z t = TwistedProbeRowDefinitions.rawIntegrand D u Z t := by
  refine rawKernel_eq_tsum D u Z hZ _ _ _ ?_ ?_ ?_
  · simp [NormalizedProbe.initialMellinPoint]
  · simp [NormalizedProbe.initialMellinPoint]
  · simp [NormalizedProbe.initialMellinPoint]

include hZ in
private theorem rawInit_eq_tsum
    (t : ℝ × ℝ × ℝ) :
    rawInitialIntegrand D u Z t = ∑' a : AIdx D,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (u, a) t :=
  rawInitialIntegrand_eq_twisted D u Z hZ t

include hZ in
theorem rawInitialIntegrand_integrable :
    Integrable (rawInitialIntegrand D u Z) := by
  obtain ⟨hmaj, hint, hsum⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  letI := aIndex_countable' D
  rw [(funext fun t => rawInit_eq_tsum D u Z hZ t)]
  refine hmaj.mono' (AEStronglyMeasurable.tsum (fun a => (hint (u, a)).1)) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have hd : NormalizedProbe.initialMellinPoint t ∈ NormalizedProbe.separatedSeriesDomain := by
    norm_num [NormalizedProbe.initialMellinPoint, NormalizedProbe.separatedSeriesDomain,
      Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  have htn : Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i t‖) := by
    simpa only [NormalizedProbe.initialTripleMellinSummand, norm_mul] using
      ((NormalizedProbe.separatedSeries_absolute_locallyUniform D.recipe.probe).1
        (NormalizedProbe.initialMellinPoint t) hd).mul_left (‖NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
        (NormalizedProbe.initialMellinPoint t).1
        (NormalizedProbe.initialMellinPoint t).2.1 (NormalizedProbe.initialMellinPoint t).2.2‖)
  have hinj : Function.Injective (fun a : AIdx D =>
      ((u, a) : NormalizedProbe.MellinSeriesIndex D.recipe.probe)) :=
    fun a b h => (Prod.mk.inj h).2
  calc _
      ≤ ∑' a : AIdx D, ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z (u, a) t‖ :=
        norm_tsum_le_tsum_norm (htn.comp_injective hinj)
    _ ≤ ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
          ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t‖ :=
        (htn.comp_injective hinj).tsum_le_tsum_of_inj _ hinj (fun _ _ => norm_nonneg _)
          (fun _ => le_rfl) htn
    _ = NormalizedProbe.initialAbsoluteMellinMajorant D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z t := by
      simp only [NormalizedProbe.initialTripleMellinSummand,
        NormalizedProbe.initialAbsoluteMellinMajorant, norm_mul, tsum_mul_left]

end

theorem rawInitialIntegrand_norm_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : Frequency D.recipe => ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u Z t‖) := by
  obtain ⟨hmaj, hint, hsum⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  letI := aIndex_countable' D
  refine Summable.of_nonneg_of_le (fun u => integral_nonneg fun t => norm_nonneg _) ?_ hsum.prod
  intro u
  simp_rw [rawInit_eq_tsum D u Z hZ]
  exact (PoissonInitialBridge.integrable_tsum_norm_bound
    (fun a : AIdx D => NormalizedProbe.initialTripleMellinSummand D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z (u, a))
    (fun a => hint _) (hsum.prod_factor _)).2

theorem initialRowIntegral_eq (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z) :
    RawFixed.FixedData.initialRowIntegral D u Z = rawinitialRowIntegral D u Z := by
  unfold rawinitialRowIntegral
  rw [integral_three' (rawInitialIntegrand_integrable D u Z hZ)]
  simp only [RawFixed.FixedData.initialRowIntegral, RawFixed.FixedData.triple,
    RawFixed.FixedData.Iwz, RawFixed.FixedData.Iz, comparisonVerticalIntegral,
    rawInitialIntegrand, integral_const_mul, Complex.ofReal_ofNat]
  ring

theorem twisted_ne_principal (f : TwistedProbeRowDefinitions.TwistedRow D) :
    f.val ≠ principalFrequency D.recipe := by
  intro h
  apply f.property
  refine ⟨ActualRowCount.principalRow D, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h2 : (f.val).val.val = 1 := by rw [h]; exact rfl
  rw [h2]
  exact ActualRowCount.principalRow_u D

def omitEquiv : TwistedProbeRowDefinitions.TwistedRow D × AIdx D ≃
    ↥(PoissonFrequencyDecomposition.allowedIndices D)ᶜ where
  toFun p := ⟨(p.1.val, p.2), by
    intro h
    obtain ⟨u, hu⟩ := h
    exact p.1.property ⟨u, hu⟩⟩
  invFun i := (⟨i.1.1, by
    intro h
    obtain ⟨u, hu⟩ := h
    exact i.2 ⟨u, hu⟩⟩, i.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem tsum_omit (g : ↥(PoissonFrequencyDecomposition.allowedIndices D)ᶜ → ℂ)
    (hg : Summable g) :
    ∑' i, g i = ∑' f : TwistedProbeRowDefinitions.TwistedRow D, ∑' a : AIdx D,
      g (omitEquiv D (f, a)) := by
  rw [← (omitEquiv D).tsum_eq g]
  have hg' := (omitEquiv D).summable_iff.mpr hg
  exact hg'.tsum_prod' (fun f => hg'.prod_factor f)

theorem omittedSum_eq_twisted (Z : ℝ) (hZ : 0 < Z) :
    PoissonFrequencyDecomposition.omittedSum D Z =
      ∑' f : TwistedProbeRowDefinitions.TwistedRow D, rawinitialRowIntegral D f.val Z := by
  letI := aIndex_countable' D
  obtain ⟨-, hint, hsum⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  let initialTripleMellinSummand₀ := NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
  have hOsum' : Summable (fun i : ↥(PoissonFrequencyDecomposition.allowedIndices D)ᶜ =>
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
      ∫ t : ℝ × ℝ × ℝ, initialTripleMellinSummand₀ i.val t) := by
    refine ((hsum.subtype _).mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖).of_norm_bounded (fun i => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  unfold PoissonFrequencyDecomposition.omittedSum
  rw [tsum_omit D _ hOsum']
  refine tsum_congr fun f => ?_
  have hrow : ∫ t : ℝ × ℝ × ℝ, rawInitialIntegrand D f.val Z t =
      ∑' a : AIdx D, ∫ t : ℝ × ℝ × ℝ, initialTripleMellinSummand₀ (f.val, a) t := by
    calc _
        = ∫ t : ℝ × ℝ × ℝ, ∑' a : AIdx D, initialTripleMellinSummand₀ (f.val, a) t :=
          integral_congr_ae
            (Filter.Eventually.of_forall fun t => rawInit_eq_tsum D f.val Z hZ t)
      _ = _ := (integral_tsum_of_summable_integral_norm (fun a : AIdx D => hint (f.val, a))
        (hsum.prod_factor f.val)).symm
  unfold rawinitialRowIntegral
  rw [hrow, tsum_mul_left]
  rfl

end

end DedekindZetaZeroFree.Quantitative.RawInitialKernel31
