module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyIdentification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawInitialKernel31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rawInitialIntegrand (u : Frequency D.recipe) (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  RawFixed.FixedData.rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
    ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I) ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I) Z

def rawinitialRowIntegral (u : Frequency D.recipe) (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rawInitialIntegrand D u Z t

theorem separatedSeries_eq_rawFactor (u : Frequency D.recipe) (ξ w z : ℂ)
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

private theorem integral_three' {f : (ℝ × ℝ × ℝ) → ℂ} (hf : Integrable f) :
    (∫ t : ℝ × ℝ × ℝ, f t) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x, y, z) := by
  rw [MeasureTheory.Measure.volume_eq_prod] at hf
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae] with x hx
  rw [MeasureTheory.Measure.volume_eq_prod] at hx
  exact integral_prod _ hx

theorem frequencyNorm_pos' (u : Frequency D.recipe) : 0 < frequencyNorm D.recipe u := by
  rw [← RawFixed.FixedData.rawFrequency_norm D u]
  exact_mod_cast D.recipe.A.exteriorNorm_pos _

theorem rawKernel_eq_tsum (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    RawFixed.FixedData.rawKernel D u ξ w z Z =
      ∑' a : AIdx D, NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z)
        Z ξ w z * NormalizedProbe.weightedSeparatedSummand D.recipe.probe (u, a) ξ w z := by
  have hq := frequencyNorm_pos' D u
  rw [tsum_mul_left]
  have hs : ∑' a : AIdx D, NormalizedProbe.weightedSeparatedSummand D.recipe.probe (u, a) ξ w z =
      comparisonRealPower (frequencyNorm D.recipe u) (-z) * separatedSeries D.recipe u ξ w z := by
    simp only [NormalizedProbe.weightedSeparatedSummand, tsum_mul_left]
    rfl
  rw [hs, PoissonInitialBridge.tripleMellinWeight_eq D Z hZ ξ w z]
  unfold RawFixed.FixedData.rawKernel
  rw [← separatedSeries_eq_rawFactor D u ξ w z hξ hw hz,
    PoissonInitialBridge.cpow_eq_comparisonRealPower hq]
  ring

private theorem rawInit_eq_tsum (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z)
    (t : ℝ × ℝ × ℝ) :
    rawInitialIntegrand D u Z t = ∑' a : AIdx D,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (u, a) t := by
  apply rawKernel_eq_tsum D u Z hZ <;> simp [Complex.mul_re]

theorem rawInitialIntegrand_integrable (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z) :
    Integrable (rawInitialIntegrand D u Z) := by
  obtain ⟨_, hint, hsum⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  letI := aIndex_countable' D
  rw [funext (rawInit_eq_tsum D u Z hZ)]
  exact (PoissonInitialBridge.integrable_tsum_norm_bound _
    (fun a : AIdx D => hint (u, a)) (hsum.prod_factor u)).1

theorem rawInitialIntegrand_norm_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : Frequency D.recipe => ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u Z t‖) := by
  obtain ⟨hmaj, hint, hsum⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  letI := aIndex_countable' D
  have hfib : ∀ u : Frequency D.recipe, ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u Z t‖ ≤
      ∑' a : AIdx D, ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand
        D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z (u, a) t‖ := by
    intro u
    simp_rw [rawInit_eq_tsum D u Z hZ]
    exact (PoissonInitialBridge.integrable_tsum_norm_bound
      (fun a : AIdx D => NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (u, a))
      (fun a => hint _) (hsum.prod_factor _)).2
  exact Summable.of_nonneg_of_le (fun u => integral_nonneg fun t => norm_nonneg _) hfib hsum.prod

theorem initialRowIntegral_eq (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z) :
    RawFixed.FixedData.initialRowIntegral D u Z = rawinitialRowIntegral D u Z := by
  have hint := rawInitialIntegrand_integrable D u Z hZ
  unfold rawinitialRowIntegral
  rw [integral_three' hint]
  simp only [RawFixed.FixedData.initialRowIntegral, RawFixed.FixedData.triple,
    RawFixed.FixedData.Iwz, RawFixed.FixedData.Iz, comparisonVerticalIntegral,
    rawInitialIntegrand, integral_const_mul, Complex.ofReal_ofNat]
  ring

abbrev NonprincipalFrequency : Type := {u : Frequency D.recipe // u ≠ principalFrequency D.recipe}

def nonprincipalSum (Z : ℝ) : ℂ :=
  ∑' u : NonprincipalFrequency D, RawFixed.FixedData.initialRowIntegral D u.val Z

private theorem kernel_eq_sum' (Z : ℝ) (t : ℝ × ℝ × ℝ) :
    ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t =
      NormalizedProbe.principalTripleMellinKernel D.recipe.A D.recipe.σ D.recipe.target
        D.recipe.traceBad D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
        (NormalizedProbe.initialMellinPoint t).1 (NormalizedProbe.initialMellinPoint t).2.1
        (NormalizedProbe.initialMellinPoint t).2.2 := by
  dsimp [NormalizedProbe.initialTripleMellinSummand]
  rw [tsum_mul_left, NormalizedProbe.separatedSeries_eq_grouped D.recipe.probe]
  · rfl
  all_goals norm_num [NormalizedProbe.initialMellinPoint, Complex.mul_re]

private theorem Iscale_eq_whole' (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ,
      ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t := by
  have hX := Scales.xScale_pos Z hZ
  have hY := Scales.yScale_pos Z hZ
  have hwhole := (NormalizedProbe.tripleMellin_sum_integral_interchange D.recipe.probe
    (Scales.xScale Z) (Scales.yScale Z) Z hX hY hZ).1
  have hexact := NormalizedProbe.ExactTripleMellin.initial_order D.recipe.A D.recipe.σ
    D.recipe.target D.recipe.traceBad D.recipe.probe
    (NormalizedProbe.probe_exact_triple_mellin D.recipe.A D.recipe.σ D.recipe.target
      D.recipe.traceBad D.recipe.probe D.recipe.normalization)
    ⟨Scales.xScale Z, hX⟩ ⟨Scales.yScale Z, hY⟩ ⟨Z, hZ⟩
  change D.Iscale Z = _ at hexact
  rw [hexact, integral_three' hwhole]
  congr 1
  · simp [NormalizedProbe.tripleMellinNormalization]
  · simp_rw [kernel_eq_sum' D Z]
    rfl

private theorem Jpr_eq_initial (Z : ℝ) (hZ : 0 < Z) :
    PoissonKernel.Jpr D Z = RawFixed.FixedData.initialRowIntegral D (principalFrequency D.recipe) Z := by
  have he : PoissonInitialBridge.toProbeFrequency D (ActualRowCount.principalRow D) =
      principalFrequency D.recipe := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hi : PoissonInitialBridge.initialRowIntegrand D (ActualRowCount.principalRow D) Z =
      rawInitialIntegrand D (principalFrequency D.recipe) Z := by
    funext t
    rw [PoissonInitialBridge.rowIntegrand_eq_tsum D _ Z hZ, he, rawInit_eq_tsum D _ Z hZ]
  have hpr : PoissonKernel.principalRows D = {ActualRowCount.principalRow D} := by
    ext u
    exact ActualRowCount.u_eq_one_iff D
  rw [initialRowIntegral_eq D _ Z hZ, rawinitialRowIntegral, ← hi,
    integral_three' (hi.symm ▸ rawInitialIntegrand_integrable D _ Z hZ)]
  unfold PoissonKernel.Jpr PoissonKernel.J
  rw [hpr, finsum_mem_singleton]
  simp only [comparisonVerticalIntegral, PoissonKernel.wzIntegral,
    PoissonInitialBridge.initialRowIntegrand, integral_const_mul, Complex.ofReal_ofNat]
  ring

theorem Iscale_eq_principal_add_nonprincipal (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = PoissonKernel.Jpr D Z + nonprincipalSum D Z := by
  letI := aIndex_countable' D
  obtain ⟨_, hint, hnorm⟩ := PoissonInitialBridge.initial_majorant D Z hZ
  let c : ℂ := (2 * (Real.pi : ℂ))⁻¹ ^ 3
  let f := NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
  let g : NormalizedProbe.MellinSeriesIndex D.recipe.probe → ℂ := fun i => c * ∫ t, f i t
  have hg : Summable g := (hnorm.mul_left ‖c‖).of_norm_bounded fun i => by
    dsimp [g, f]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  have hrow (u : Frequency D.recipe) : (∑' a : AIdx D, g (u, a)) =
      RawFixed.FixedData.initialRowIntegral D u Z := by
    simp only [g, tsum_mul_left, initialRowIntegral_eq D u Z hZ, rawinitialRowIntegral]
    congr 1
    simp_rw [rawInit_eq_tsum D u Z hZ]
    exact (integral_tsum_of_summable_integral_norm (fun a : AIdx D => hint (u, a))
      (hnorm.prod_factor u))
  have hsum := hg.prod.congr hrow
  rw [Iscale_eq_whole' D Z hZ, (NormalizedProbe.tripleMellin_sum_integral_interchange
    D.recipe.probe _ _ _ (Scales.xScale_pos Z hZ) (Scales.yScale_pos Z hZ) hZ).2]
  change c * (∑' i, ∫ t, f i t) = _
  rw [← tsum_mul_left]
  change ∑' i, g i = _
  rw [hg.tsum_prod' hg.prod_factor, tsum_congr hrow, Jpr_eq_initial D Z hZ,
    hsum.tsum_eq_add_tsum_ite (principalFrequency D.recipe), nonprincipalSum]
  congr 1
  refine Eq.trans ?_ (tsum_subtype {u : Frequency D.recipe | u ≠ principalFrequency D.recipe}
    (fun u => RawFixed.FixedData.initialRowIntegral D u Z)).symm
  apply tsum_congr
  intro u
  by_cases hu : u = principalFrequency D.recipe <;> simp [Set.indicator_apply, hu]

end

end DedekindZetaZeroFree.Quantitative.RawInitialKernel31
