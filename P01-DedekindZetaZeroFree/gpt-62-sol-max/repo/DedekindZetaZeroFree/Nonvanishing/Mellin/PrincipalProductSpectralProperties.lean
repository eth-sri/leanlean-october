module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalThetaContext
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData
public import DedekindZetaZeroFree.Moments.Principal.Corrections.SummableMajorants
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds
public import DedekindZetaZeroFree.Moments.Principal.Numerator.RightHalfPlaneBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalIncompleteEulerNonvanishing

@[expose] public section

open scoped Classical
open Filter
noncomputable section
namespace DedekindZetaZeroFree.PrincipalMellin
private theorem product_analytic {ι : Type} (f : ι → ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (u : ι → ℝ) (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ i z, z ∈ U → ‖f i z - 1‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∏' i, f i z) U := by
  have hs := summable_finsetProd_of_summable_nonneg hu0 hu
  have hd : DifferentiableOn ℂ
      (fun z => ∑' T : Finset ι, ∏ i ∈ T, (f i z - 1)) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hs
    · fun_prop
    · exact hU
    · intro T z hz
      refine (Finset.norm_prod_le _ _).trans ?_
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hb i z hz)
  apply hd.congr
  intro z hz
  have hnorm : Summable (fun i => ‖f i z - 1‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i z hz)
  have hh := tprod_one_add (summable_finsetProd_of_summable_norm hnorm)
  simpa using hh
private theorem product_bound {ι : Type} (f : ι → ℂ) (u : ι → ℝ)
    (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i) (hb : ∀ i, ‖f i - 1‖ ≤ u i) :
    ‖∏' i, f i‖ ≤ ∑' T : Finset ι, ∏ i ∈ T, u i := by
  have hnorm : Summable (fun i => ‖f i - 1‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have heq := tprod_one_add (summable_finsetProd_of_summable_norm hnorm)
  have hs := summable_finsetProd_of_summable_nonneg hu0 hu
  have hbT : ∀ T : Finset ι, ‖∏ i ∈ T, (f i - 1)‖ ≤ ∏ i ∈ T, u i := by
    intro T
    exact (Finset.norm_prod_le _ _).trans
      (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hb i))
  have hsum := hs.of_norm_bounded hbT
  have heq' : (∏' i, f i) = ∑' T : Finset ι, ∏ i ∈ T, (f i - 1) := by simpa using heq
  rw [heq']
  exact (norm_tsum_le_tsum_norm hsum.norm).trans
    (hsum.norm.tsum_le_tsum hbT hs)

end DedekindZetaZeroFree.PrincipalMellin
namespace DedekindZetaZeroFree.PrincipalMellin
open scoped NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
 def primePlace {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (p : ExteriorIdealEuler.PrimeIndex R.A.cS) :
    HeightOneSpectrum (𝓞 F) :=
  ⟨p.val.val, Ideal.isPrime_of_prime p.property, p.val.property.1⟩
 def primeOutside {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (p : ExteriorIdealEuler.PrimeIndex R.A.cS) :
    {v : HeightOneSpectrum (𝓞 F) // v ∉ R.A.Sf} := by
  refine ⟨primePlace R p, ?_⟩
  intro hp
  have h := (R.A.exterior_iff ⟨p.val.val, p.val.property.1⟩).mp p.val.property.2
    (primePlace R p) hp
  simp [primePlace] at h
  exact p.property.not_unit (by simpa [h] using (isUnit_one : IsUnit (1 : Ideal (𝓞 F))))
private theorem primeOutside_injective {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) : Function.Injective (primeOutside R) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v => v.val.asIdeal) h
private theorem local_phases {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (p : ExteriorIdealEuler.PrimeIndex R.A.cS) :
    ‖R.target p.val.val‖ = 1 ∧
      ‖R.probe.coefficients.theta (R.probe.coefficients.generator p.val) ^ 6‖ = 1 := by
  constructor
  · exact RayUnitary.ray_character_norm_eq_one F R.A.modulus R.A.modulus_ne_zero
      R.target _ p.val.property.1 (PrincipalProbeConstruction.Inputs.exterior_coprime R.A p.val)
  · rw [norm_pow, NormalizedProbe.principal_theta_norm R.probe
      ⟨R.probe.coefficients.generator p.val, (R.probe.coefficients.generates p.val).1⟩]
    simp
private theorem local_ne_zero {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (p : ExteriorIdealEuler.PrimeIndex R.A.cS)
    (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) : R.localCorrection p s ≠ 0 := by
  have hq : 1 < idealNorm p.val.val := by
    change 1 < (Ideal.absNorm p.val.val : ℝ)
    have h := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm (primePlace R p)
    exact_mod_cast h
  have hphase := local_phases R p
  unfold ActualRecipe.localCorrection
  rw [← Complex.ofReal_inv]
  apply Audit.Euler.principalCorrection_ne_zero
  · positivity
  · exact inv_lt_one_of_one_lt₀ hq
  · rw [norm_mul, hphase.1, one_mul, NormalizedProbe.comparisonRealPower_norm _ (by linarith)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hq
    simp only [Complex.neg_re]; linarith
  · rw [norm_mul, hphase.2, one_mul, NormalizedProbe.comparisonRealPower_norm _ (by linarith)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hq
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith

private theorem local_majorized {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (a : ℝ) (ha : (2 / 3 : ℝ) < a) :
    ∃ u : ExteriorIdealEuler.PrimeIndex R.A.cS → ℝ,
      Summable u ∧ (∀ p, 0 ≤ u p) ∧
      ∀ p s, a ≤ s.re → ‖R.localCorrection p s - 1‖ ≤ u p := by
  obtain ⟨C, hC, hb⟩ := principal_local_majorant a ha
  let u : ExteriorIdealEuler.PrimeIndex R.A.cS → ℝ := fun p => C *
    ((idealNorm p.val.val) ^ (-2 : ℝ) + (idealNorm p.val.val) ^ (-1 - a) +
      (idealNorm p.val.val) ^ (3 - 6 * a))
  refine ⟨u, ?_, ?_, ?_⟩
  · exact ((principal_majorant_summable F R.A.Sf a ha).comp_injective
      (primeOutside_injective R)).mul_left C
  · intro p
    dsimp [u]
    have hq : 0 ≤ idealNorm p.val.val := by unfold idealNorm; positivity
    positivity
  · intro p s hs
    have hq : 2 ≤ idealNorm p.val.val := by
      change 2 ≤ (Ideal.absNorm p.val.val : ℝ)
      have h := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm (primePlace R p)
      exact_mod_cast h
    exact (hb _ hq _ _ (local_phases R p).1 (local_phases R p).2 s hs).1
private theorem local_diff {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (p : ExteriorIdealEuler.PrimeIndex R.A.cS) :
    DifferentiableOn ℂ (R.localCorrection p) {s : ℂ | (2 / 3 : ℝ) < s.re} := by
  intro s hs
  change (2 / 3 : ℝ) < s.re at hs
  have hq : 1 < idealNorm p.val.val := by
    change 1 < (Ideal.absNorm p.val.val : ℝ)
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm (primePlace R p)
  have hphase := local_phases R p
  have hD : 1 - R.target p.val.val * comparisonRealPower (idealNorm p.val.val) (-s) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh : ‖R.target p.val.val * comparisonRealPower (idealNorm p.val.val) (-s)‖ < 1 := by
      rw [norm_mul, hphase.1, one_mul, NormalizedProbe.comparisonRealPower_norm _ (by linarith)]
      apply Real.rpow_lt_one_of_one_lt_of_neg hq
      simp only [Complex.neg_re]; linarith [hs]
    simp [← h] at hh
  have hE : 1 - R.probe.coefficients.theta (R.probe.coefficients.generator p.val) ^ 6 *
      comparisonRealPower (idealNorm p.val.val) (3 - 6 * s) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh : ‖R.probe.coefficients.theta (R.probe.coefficients.generator p.val) ^ 6 *
        comparisonRealPower (idealNorm p.val.val) (3 - 6 * s)‖ < 1 := by
      rw [norm_mul, hphase.2, one_mul, NormalizedProbe.comparisonRealPower_norm _ (by linarith)]
      apply Real.rpow_lt_one_of_one_lt_of_neg hq
      norm_num [Complex.sub_re, Complex.mul_re]
      linarith [hs]
    simp [← h] at hh
  unfold ActualRecipe.localCorrection Audit.Euler.principalCorrection comparisonRealPower
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero hE hD
theorem actual_principal_H_differentiable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) :
    DifferentiableOn ℂ R.H {s : ℂ | (2 / 3 : ℝ) < s.re} := by
  intro s hs
  change (2 / 3 : ℝ) < s.re at hs
  let a : ℝ := ((2 / 3 : ℝ) + s.re) / 2
  have ha : (2 / 3 : ℝ) < a := by dsimp [a]; linarith [hs]
  have has : a < s.re := by dsimp [a]; linarith [hs]
  let U : Set ℂ := {z : ℂ | a < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨u, hu, hu0, hb⟩ := local_majorized R a ha
  have hd := product_analytic R.localCorrection U hU u hu hu0
    (fun p => (local_diff R p).mono (fun z hz => lt_trans ha hz))
    (fun p z hz => hb p z hz.le)
  exact (hd.differentiableAt (hU.mem_nhds has)).differentiableWithinAt

theorem actual_principal_H_ne_zero {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) : R.H s ≠ 0 := by
  obtain ⟨u, hu, hu0, hb⟩ := local_majorized R s.re hs
  have hsum : Summable (fun p => ‖R.localCorrection p s - 1‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hb p s le_rfl)
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun p => R.localCorrection p s - 1)
    (fun p => by simpa using local_ne_zero R p s hs) hsum
  simpa [ActualRecipe.H] using h
theorem actual_principal_H_bound {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (a : ℝ) (ha : (2 / 3 : ℝ) < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → ‖R.H s‖ ≤ C := by
  obtain ⟨u, hu, hu0, hb⟩ := local_majorized R a ha
  refine ⟨∑' T : Finset (ExteriorIdealEuler.PrimeIndex R.A.cS), ∏ p ∈ T, u p, ?_, ?_⟩
  · exact tsum_nonneg (fun T => Finset.prod_nonneg (fun p _ => hu0 p))
  · intro s hs
    exact product_bound (fun p => R.localCorrection p s) u hu hu0 (fun p => hb p s hs)

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem spectral_strip_bound (R : ActualRecipe S η) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
 ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
  ‖R.G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
 obtain ⟨M, hM, hH⟩ := actual_principal_H_bound R a (by linarith)
 obtain ⟨B, hB, hL⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound R a ha
 let C := Real.exp ((b - 5 / 6) ^ 2) * (M * B)
 refine ⟨C, by dsimp [C]; positivity, ?_⟩
 intro r hr t
 have hre : ((r : ℂ) + t * Complex.I).re = r := by simp
 have hg : ‖Complex.exp ((((r : ℂ) + t * Complex.I) - 5 / 6) ^ 2)‖ ≤
  Real.exp ((b - 5 / 6) ^ 2) / (1 + t ^ 2) := by
  rw [Complex.norm_exp]
  have hexp : ((((r : ℂ) + t * Complex.I) - 5 / 6) ^ 2).re =
   (r - 5 / 6) ^ 2 - t ^ 2 := by
   simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hexp, Real.exp_sub]
  have hsquare : (r - 5 / 6) ^ 2 ≤ (b - 5 / 6) ^ 2 := by
   nlinarith [hr.1, hr.2]
  apply div_le_div₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr hsquare)
   (by positivity : 0 < 1 + t ^ 2)
  simpa [add_comm] using Real.add_one_le_exp (t ^ 2)
 unfold ActualRecipe.G ActualRecipe.N
 rw [div_eq_mul_inv, norm_mul, norm_mul]
 have hhs := hH ((r : ℂ) + t * Complex.I) (by simpa [hre] using hr.1)
 have hls := hL ((r : ℂ) + t * Complex.I) (by simpa [hre] using hr.1)
 calc
  _ ≤ (Real.exp ((b - 5 / 6) ^ 2) / (1 + t ^ 2)) * M * B := by
   exact mul_le_mul (mul_le_mul hg hhs (norm_nonneg _) (by positivity)) hls
    (norm_nonneg _) (by positivity)
  _ = C / (1 + t ^ 2) := by dsimp [C]; ring

theorem actual_principal_spectral_properties
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (R : ActualRecipe S η) :
    AnalyticOnNhd ℂ R.N {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1} ∧
    (∀ s ∈ {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1}, R.N s ≠ 0) ∧
    DifferentiableOn ℂ R.G {s : ℂ | 1 < s.re} ∧
    (∀ a b : ℝ, 1 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
        ‖R.G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) ∧
    (∀ s : ℂ, 1 < s.re → R.L s ≠ 0) := by
  have hexp (s : ℂ) (hs : 1 < s.re) : Complex.exp
      (HeckeLogProof.eulerLog
        (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => R.target I.val) s) =
      R.continuation.L s := by
    rw [HeckeLogProof.exp_eulerLog _
      (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target) s hs]
    have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
        R.target I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
        {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
      intro I hI
      refine ⟨?_, by simp⟩
      intro hzero
      have hη : R.target I = 0 := (R.target.eq_zero_iff' I).mpr (Or.inl hzero)
      exact hI (by simpa only [hη, zero_mul])
    exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr
      (R.continuation.series s hs)).tsum_eq
  have hLzero (s : ℂ) (hs : 1 < s.re) : R.L s ≠ 0 := by
    apply MellinZeroFree.comparisonPrincipalIncompleteL_ne_zero_of_L_ne_zero
      F R.A R.target R.probe.principal R.continuation s (by linarith)
    rw [← hexp s hs]
    exact Complex.exp_ne_zero _
  have hN : DifferentiableOn ℂ R.N {s : ℂ | (2 / 3 : ℝ) < s.re} :=
    (((differentiable_id.sub_const (5 / 6)).pow 2).cexp.differentiableOn).mul
      (actual_principal_H_differentiable R)
  refine ⟨?_, ?_, ?_, ?_, hLzero⟩
  · have ho : IsOpen {s : ℂ | (2 / 3 : ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (hN.analyticOnNhd ho).mono (fun s hs => by dsimp at hs ⊢; linarith [hs.1])
  · intro s hs
    exact mul_ne_zero (Complex.exp_ne_zero _) (actual_principal_H_ne_zero R s (by
      dsimp at hs ⊢; linarith [hs.1]))
  · have hNr : DifferentiableOn ℂ R.N {s : ℂ | 1 < s.re} :=
      hN.mono (fun s hs => by dsimp at hs ⊢; linarith)
    have hL : DifferentiableOn ℂ R.L {s : ℂ | 1 < s.re} := by
      have hP := R.continuation.L_holo.mono (show {s : ℂ | 1 < s.re} ⊆
          {s : ℂ | 0 < s.re ∧ s ≠ 1} from fun s hs => ⟨by
            dsimp at hs ⊢; linarith, by intro h; simp [h] at hs⟩)
      apply hP.mul
      apply DifferentiableOn.fun_finset_prod
      intro v hv
      exact ((((differentiable_id.neg).mul_const
        (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
          (R.target v.asIdeal)).differentiableOn.const_sub 1
    exact hNr.div hL (fun s hs => hLzero s hs)
  · exact spectral_strip_bound R

end DedekindZetaZeroFree.PrincipalMellin

end
