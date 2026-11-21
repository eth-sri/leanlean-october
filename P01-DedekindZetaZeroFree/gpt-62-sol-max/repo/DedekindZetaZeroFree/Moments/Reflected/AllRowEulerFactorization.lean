module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalEuler.InitialBoundary
public import DedekindZetaZeroFree.Theta.Whittaker.LocalEuler.UnitCovariance
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.SeparatedHeckeFactors

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.AllRowEuler.InitialSeparation
open LocalFiniteSums CRTEulerSeparation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

def plusExteriorCoefficient (σ : F →+* ℂ) (U : RawFrequency A) (I : A.Exterior) : ℂ :=
  UnitCovariance.residueCoefficient σ I U.u

def minusExteriorCoefficient (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : RawFrequency A) (I : A.Exterior) : ℂ :=
  η I.val * star (plusExteriorCoefficient σ U I)

def plusL (σ : F →+* ℂ) (U : RawFrequency A) (s : ℂ) : ℂ :=
  InitialSeparatedEuler.dirichletSeries (plusExteriorCoefficient σ U) s

def minusL (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : RawFrequency A) (s : ℂ) : ℂ :=
  InitialSeparatedEuler.dirichletSeries (minusExteriorCoefficient σ η U) s

def localCorrection (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) (ξ w z : ℂ) : ℂ :=
  if (U.j p).val = 0 then CorrectionFactors.goodFactor C p U.u ξ w z
  else CorrectionFactors.badFactor C p (U.j p) (U.theta C p) ξ w z

def correctionProduct (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (ξ w z : ℂ) : ℂ :=
  ∏' p : ExteriorPrime A, localCorrection C U p ξ w z

private lemma plus_base_raw (U : RawFrequency A) (I : A.Exterior) :
    plusExteriorCoefficient σ U I = σ (A.sexticResidue I U.u) :=
  UnitCovariance.residueCoefficient_eq I U.u

theorem plus_ext_mul_raw (U : RawFrequency A) (I J : A.Exterior) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.mul I J) =
      plusExteriorCoefficient σ U I * plusExteriorCoefficient σ U J := by
  simp only [plus_base_raw]
  rw [show A.sexticResidue (ExteriorIdealEuler.mul I J) U.u =
    A.sexticResidue I U.u * A.sexticResidue J U.u from
      A.sexticResidueFamily_normalized.2.2 I J _ rfl U.u, map_mul]

private lemma plus_ext_one_raw (U : RawFrequency A) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.one A.cS) = 1 := by
  rw [plus_base_raw]
  rw [show A.sexticResidue (ExteriorIdealEuler.one A.cS) U.u = 1 from
    A.residueValue_top _ _ rfl _, map_one]

private lemma plus_ext_norm_raw (U : RawFrequency A) (I : A.Exterior) :
    ‖plusExteriorCoefficient σ U I‖ ≤ 1 := by
  rw [plus_base_raw]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) U.u)
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
    have hp := A.sexticResidueFamily_normalized.1 I hx.unit
    have hp' : σ ((A.sexticResidueFamily I hx.unit : Fˣ) : F) ^ 6 = 1 := by
      rw [← map_pow]
      simpa using congrArg (fun u : Fˣ => σ (u : F)) hp
    exact (Complex.norm_eq_one_of_pow_eq_one hp' (by decide)).le
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [MulChar.map_nonunit _ hx, map_zero, norm_zero]
    exact zero_le_one

private lemma plus_ext_pow_raw (U : RawFrequency A) (I : A.Exterior) (k : ℕ) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.pow I k) =
      plusExteriorCoefficient σ U I ^ k := by
  induction k with
  | zero => simpa [ExteriorIdealEuler.pow, ExteriorIdealEuler.one] using plus_ext_one_raw (σ := σ) U
  | succ k ih =>
    have he : ExteriorIdealEuler.pow I (k+1) =
        ExteriorIdealEuler.mul (ExteriorIdealEuler.pow I k) I := by
      apply Subtype.ext; simp [ExteriorIdealEuler.pow, ExteriorIdealEuler.mul, pow_succ]
    rw [he, plus_ext_mul_raw, ih, pow_succ]

theorem raw_plus_isCoefficient (U : RawFrequency A) :
    ExteriorIdealEuler.IsCoefficient (plusExteriorCoefficient σ U) :=
  ⟨plus_ext_one_raw U, fun I J _ => plus_ext_mul_raw U I J,
    plus_ext_norm_raw U, fun p k => plus_ext_pow_raw U p.val k⟩

theorem raw_minus_isCoefficient (U : RawFrequency A) :
    ExteriorIdealEuler.IsCoefficient (minusExteriorCoefficient σ η U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [minusExteriorCoefficient, plus_ext_one_raw]
    simp [ExteriorIdealEuler.one, RayClassCharacter.map_top']
  · intro I J h
    rw [minusExteriorCoefficient, plus_ext_mul_raw]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.mul, RayClassCharacter.map_mul',
      star_mul]
    ring
  · intro I
    rw [minusExteriorCoefficient, norm_mul, norm_star]
    exact mul_le_one₀ (RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η I.val)
      (norm_nonneg _) (plus_ext_norm_raw U I)
  · intro p k
    have hη : η (p.val.val ^ k) = η p.val.val ^ k := by
      induction k with
      | zero => simp [RayClassCharacter.map_top']
      | succ k ih => rw [pow_succ, RayClassCharacter.map_mul', ih, pow_succ]
    rw [minusExteriorCoefficient, plus_ext_pow_raw]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.pow, hη, star_pow, mul_pow]

theorem raw_minusL_ne_zero (U : RawFrequency A) (s : ℂ) (hs : 1 < s.re) :
    minusL σ η U s ≠ 0 := by
  have h := (ExteriorIdealEuler.exterior_ideal_euler (minusExteriorCoefficient σ η U)
    (raw_minus_isCoefficient U) s hs).2.2.1
  simpa [minusL, InitialSeparatedEuler.dirichletSeries] using h

theorem raw_correction_deviations_summable
    (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (x : CorrectionFactors.Coordinates) (hx : x ∈ CorrectionFactors.Omega) :
    Summable (fun p : ExteriorPrime A =>
      ‖localCorrection C U p x.1 x.2.1 x.2.2 - 1‖) := by
  obtain ⟨M, hM, hbound⟩ := CorrectionFactors.good_correction_uniform_bound
  apply (CorrectionFactors.exterior_norm_majorant_summable (A := A) M (1 + 1 / 4000) (by norm_num)).of_norm_bounded_eventually
  filter_upwards [U.eventually_j_eq_zero] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa [localCorrection, hp] using
    hbound F A σ η hS C p U.u (U.isUnit_of_j_eq_zero C p hp) x hx

theorem raw_correction_multipliable
    (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (x : CorrectionFactors.Coordinates) (hx : x ∈ CorrectionFactors.Omega) :
    Multipliable (fun p : ExteriorPrime A =>
      localCorrection C U p x.1 x.2.1 x.2.2) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (raw_correction_deviations_summable C U x hx)

open IsDedekindDomain CorrectionFactors
set_option autoImplicit false

open GlobalPairCancel

 def rawPrimeEquiv : ExteriorPrime A ≃ ExteriorIdealEuler.PrimeIndex A.cS where
  toFun p := ⟨primeIdeal p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, (Ideal.prime_iff_isPrime p.val.property.1).mp p.property,
    p.val.property.1⟩, p.val.property.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

private lemma raw_normPower_eq (p : ExteriorPrime A) (s : ℂ) :
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ s = qPower p s := by
  have hn : (0 : ℝ) < (Ideal.absNorm p.val.asIdeal : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one
      (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))
  have hne : (Ideal.absNorm p.val.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hne]
  have hl : Complex.log (Ideal.absNorm p.val.asIdeal : ℂ) =
      (Real.log (Ideal.absNorm p.val.asIdeal : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hn.le).symm
  rw [hl]
  change Complex.exp _ = Complex.exp (s * _)
  congr 1
  simp only [Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
  ring

private lemma raw_term_plus (U : RawFrequency A) (p : ExteriorPrime A) (s : ℂ) :
    ExteriorIdealEuler.primeTerm (plusExteriorCoefficient σ U) s (rawPrimeEquiv p) =
      CorrectionFactors.W (σ := σ) p U.u s := by
  change plusExteriorCoefficient σ U (primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [raw_normPower_eq]
  rfl

private lemma raw_term_minus (U : RawFrequency A) (p : ExteriorPrime A) (s : ℂ) :
    ExteriorIdealEuler.primeTerm (minusExteriorCoefficient σ η U) s (rawPrimeEquiv p) =
      CorrectionFactors.D (σ := σ) (η := η) p U.u s := by
  change minusExteriorCoefficient σ η U (primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [raw_normPower_eq]
  rfl

private lemma raw_term_zeta (p : ExteriorPrime A) (z : ℂ) :
    ExteriorIdealEuler.primeTerm (fun _ : A.Exterior => (1 : ℂ)) (6 * z)
      (rawPrimeEquiv p) = CorrectionFactors.V p z := by
  change 1 * (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-(6 * z)) = _
  rw [one_mul, raw_normPower_eq]
  unfold CorrectionFactors.V
  congr 1
  ring

theorem initial_absolute_euler
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (U : RawFrequency A) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior =>
      ‖comparisonEulerPoissonSummand F A D U.u ξ w z
        i.1 i.2.1 i.2.2.1 i.2.2.2‖) ∧
    Multipliable (fun p : ExteriorPrime A => localCorrection C U p ξ w z) ∧
    minusL σ η U ξ ≠ 0 ∧
    comparisonEulerPoissonSeries F A D U.u ξ w z * minusL σ η U ξ =
      InitialSeparatedEuler.zetaS A (6 * z) * plusL σ U w *
        correctionProduct C U ξ w z := by
  have hξ' : 3 / 2 < ξ.re := by rw [hξ]; norm_num
  have hw' : 2 < w.re := by rw [hw]; norm_num
  have hz' : 1 / 6 < z.re := by rw [hz]; norm_num
  have hx : (ξ, w, z) ∈ CorrectionFactors.Omega := by
    apply Or.inl
    change _ ∧ _ ∧ _
    rw [hξ, hw, hz]
    norm_num
  refine ⟨comparisonSeries_summable A D σ η hS C.correction hD U.u ξ w z
    hξ' hw' hz', raw_correction_multipliable C U (ξ, w, z) hx,
    raw_minusL_ne_zero U ξ (by rw [hξ]; norm_num), ?_⟩
  have hξ1 : 1 < ξ.re := by rw [hξ]; norm_num
  have hw1 : 1 < w.re := by rw [hw]; norm_num
  have hz1 : 1 < (6 * z).re := by norm_num [hz]
  have hm := ExteriorIdealEuler.exterior_ideal_euler _ (raw_minus_isCoefficient (σ := σ) (η := η) U) ξ hξ1
  have hp := ExteriorIdealEuler.exterior_ideal_euler _ (raw_plus_isCoefficient (σ := σ) U) w hw1
  have hzeta := ExteriorIdealEuler.exterior_ideal_euler _
    (ExteriorIdealEuler.constant_one_isCoefficient A.cS) (6 * z) hz1
  have hne : minusL σ η U ξ ≠ 0 := raw_minusL_ne_zero U ξ hξ1
  have hDen : HasProd (fun p : ExteriorPrime A =>
      1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) (minusL σ η U ξ)⁻¹ := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hm.2.2.2
    simpa only [Function.comp_def, raw_term_minus, minusL,
      InitialSeparatedEuler.dirichletSeries] using h
  have hW : HasProd (fun p : ExteriorPrime A =>
      (1 - CorrectionFactors.W (σ := σ) p U.u w)⁻¹) (plusL σ U w) := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hp.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, raw_term_plus,
      plusL, InitialSeparatedEuler.dirichletSeries] using h
  have hV : HasProd (fun p : ExteriorPrime A =>
      (1 - CorrectionFactors.V p z)⁻¹) (InitialSeparatedEuler.zetaS A (6 * z)) := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hzeta.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, raw_term_zeta,
      ExteriorIdealEuler.summand, one_mul, InitialSeparatedEuler.zetaS] using h
  have hH := (raw_correction_multipliable C U (ξ, w, z) hx).hasProd
  have hprod := ((hDen.mul hV).mul hW).mul hH
  have hlocal (p : ExteriorPrime A) :
      f C p (U.j p) (U.theta C p) ξ w z =
      (1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) *
        (1 - CorrectionFactors.V p z)⁻¹ *
        (1 - CorrectionFactors.W (σ := σ) p U.u w)⁻¹ *
        localCorrection C U p ξ w z := by
    have hsub {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
      intro he
      have he' : a = 1 := (sub_eq_zero.mp he).symm
      simpa [he'] using ha
    have hv : 1 - CorrectionFactors.V p z ≠ 0 := by
      apply hsub
      rw [← raw_term_zeta]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _
        (ExteriorIdealEuler.constant_one_isCoefficient A.cS) (6 * z) hz1 _
    have hwne : 1 - CorrectionFactors.W (σ := σ) p U.u w ≠ 0 := by
      apply hsub
      rw [← raw_term_plus U]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _ (raw_plus_isCoefficient U) w hw1 _
    have hdne : 1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ ≠ 0 := by
      apply hsub
      rw [← raw_term_minus U]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _ (raw_minus_isCoefficient U) ξ hξ1 _
    by_cases hj : (U.j p).val = 0
    · have hu : U.u = U.unitPart C p := by
        simpa [hj] using (U.unitPart_spec C p).1
      have hunit := U.isUnit_of_j_eq_zero C p hj
      have hθ : (U.theta C p).val = chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
        rw [hu]
        rfl
      have hf : f C p (U.j p) (U.theta C p) ξ w z =
          CorrectionFactors.goodRational C p U.u ξ w z := by
        have hformula := (good_euler_series_initial_boundary C p U.u hunit
          (U.theta C p) hθ ξ w z (by rw [hξ]) (by rw [hw]) (by rw [hz])).2
        have hj0 : U.j p = 0 := Fin.ext hj
        rw [hj0]
        simpa [CorrectionFactors.goodRational, CorrectionFactors.V,
          CorrectionFactors.W, CorrectionFactors.D, CorrectionFactors.E, hθ] using hformula
      rw [hf]
      simp only [localCorrection, hj, ↓reduceIte, CorrectionFactors.goodFactor]
      field_simp
    · obtain ⟨hW, hD⟩ := CorrectionFactors.primitive_variables_zero C U p hj ξ w
      simp only [localCorrection, hj, ↓reduceIte, CorrectionFactors.badFactor, hW, hD]
      field_simp
  have hseries : HasProd (fun p : ExteriorPrime A =>
      f C p (U.j p) (U.theta C p) ξ w z)
      (comparisonEulerPoissonSeries F A D U.u ξ w z) :=
    CRTEulerSeparation.hasProd_local_series C U D hD ξ w z hξ' hw' hz'
  have heq := hseries.unique (hprod.congr_fun hlocal)
  rw [heq]
  change (minusL σ η U ξ)⁻¹ * InitialSeparatedEuler.zetaS A (6 * z) *
    plusL σ U w * correctionProduct C U ξ w z * minusL σ η U ξ = _
  field_simp

theorem initial_euler_quotient
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (U : RawFrequency A) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    comparisonEulerPoissonSeries F A D U.u ξ w z =
      InitialSeparatedEuler.zetaS A (6 * z) * plusL σ U w *
        correctionProduct C U ξ w z / minusL σ η U ξ := by
  obtain ⟨_, _, hn, he⟩ := initial_absolute_euler C D hD U ξ w z hξ hw hz
  exact (eq_div_iff hn).mpr he

end DedekindZetaZeroFree.AllRowEuler.InitialSeparation

end
