module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalInitialContourRegularity
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalFirstPoleContour
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalResidueKernelContourBounds
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalContourRemainderDecomposition
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalResidueNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

open Filter Asymptotics

noncomputable section
open scoped Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

@[simp] theorem frequencyNorm_principalFrequency
    (R : PrincipalMellin.ActualRecipe S η) :
    frequencyNorm R (principalFrequency R) = 1 := by
  simp only [frequencyNorm, principalFrequency, FiniteTransform.exteriorNorm,
    FiniteTransform.Residue, Ideal.span_singleton_one]
  haveI : Subsingleton (R.A.R.toSubring ⧸ (⊤ : Ideal R.A.R.toSubring)) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  simp

def principalRegularization (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) : ℂ :=
  R.continuation.R s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

@[simp] theorem principalRegularization_at_one
    (R : PrincipalMellin.ActualRecipe S η) :
    principalRegularization R 1 =
      comparisonPrincipalResidue F R.A R.target R.probe.principal R.continuation := rfl

theorem principal_coefficient_field_trace
    (R : PrincipalMellin.ActualRecipe S η) (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

def principalArithmeticContext (R : PrincipalMellin.ActualRecipe S η) :
    R.A.GeneralArithmeticContext R.σ R.target R.traceBad := by
  let A := R.A
  let D := R.probe.correction
  letI : Subsingleton (ClassGroup A.R) := R.classKilled
  have hl := ArithmeticContext.actual_hilbert_lagrangian_properties
    A R.classKilled D.H D.B D.H_actual D.B_complement
  exact {
    principal := A.principalIdealRing_of_classGroup_subsingleton R.classKilled
    classGroup_trivial := R.classKilled
    fractional_principal := fun I hI => exists_unit_of_isPrincipal I
      (ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI) hI.ne_zero
    unit_injective := A.unitQuotientClass_injective R.classKilled
    unit_image := A.unitQuotientClass_range
    correction := D
    units_lagrangian := hl.1
    primary_two := hl.2.1
    primary_three := hl.2.2
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A D.H D.B D.H_actual D.B_complement
    allowed_integral := fun I =>
      A.exists_allowed_integral_generator R.classKilled D.H D.B D.B_complement I
    allowed_unique := fun I a b ha hb =>
      A.allowed_generator_unique_mod_sixth R.classKilled D.H D.B D.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }

theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    PrincipalProbeConstruction.ArithmeticBinding R.A R.σ R.target R.traceBad
      C R.probe.allowed R.probe.coefficients := by
  refine ⟨R.probe.sameComplement.trans (congrArg (fun D => D.B) hC),
    R.probe.sameGenerator, R.probe.exteriorCharacters, ?_, R.probe.gammaTwo_recipe,
    R.probe.sixthUnitCharacters, principal_coefficient_field_trace R, ?_⟩
  · intro m
    rw [R.probe.theta_principal, hC]
  · intro x
    rw [principal_coefficient_field_trace R,
      PrincipalProbeConstruction.Inputs.fieldTrace_phase]

theorem principal_arithmetic_compatibility (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad C.correction := by
  exact PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)

theorem principal_actual_arithmetic_compatibility
    (R : PrincipalMellin.ActualRecipe S η) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad (principalArithmeticContext R).correction := by
  exact principal_arithmetic_compatibility R (principalArithmeticContext R) rfl

def principalEulerFrequency (R : PrincipalMellin.ActualRecipe S η) :
    CorrectionFactors.Frequency (principalArithmeticContext R) where
  u := 1
  ideal := ⟨⊤, top_ne_bot, by simp⟩
  generates := by
    constructor
    · exact one_ne_zero
    · simp [SArithmeticData.extendIdeal, Ideal.map_top]
  allowed := by
    convert (principalArithmeticContext R).correction.B.one_mem using 1
    simp [SArithmeticData.IsAllowed]
  sixthFree := by
    intro p
    simp only [idealPrimeExponent]
    have ht : UniqueFactorizationMonoid.normalizedFactors
        (⊤ : Ideal (NumberField.RingOfIntegers F)) = 0 :=
      by simpa only [Ideal.one_eq_top] using
        (UniqueFactorizationMonoid.normalizedFactors_one
          (α := Ideal (NumberField.RingOfIntegers F)))
    rw [ht]
    simp

def principalContourCorrection (R : PrincipalMellin.ActualRecipe S η) (ξ w z : ℂ) : ℂ :=
  ∏' p : LocalFiniteSums.ExteriorPrime R.A,
    CorrectionFactors.localFactor (principalArithmeticContext R) (principalEulerFrequency R)
      p ξ w z

theorem principalContourCorrection_principal_specialization (R : PrincipalMellin.ActualRecipe S η)
    (ξ : ℂ) (hξ : (499 / 500 : ℝ) - 1 / 100000 < ξ.re) :
    principalContourCorrection R ξ 1 (1 / 6) =
      CorrectionFactors.H_eta (principalArithmeticContext R) ξ := by
  obtain ⟨hm, hh⟩ :=
    (PrincipalCorrection.principal_specialization (principalArithmeticContext R)
      (principalEulerFrequency R) rfl).2 ξ hξ
  exact hh

theorem principal_theta_at_euler_generator (R : PrincipalMellin.ActualRecipe S η)
    (p : LocalFiniteSums.ExteriorPrime R.A) :
    R.probe.coefficients.theta (R.probe.coefficients.generator (LocalFiniteSums.primeIdeal p)) =
      LocalFiniteSums.vartheta (principalArithmeticContext R) p := by
  let C := principalArithmeticContext R
  let D := R.probe.coefficients
  have hD := principal_actual_arithmetic_compatibility R
  rw [hD.theta_recipe _ (D.generates _).1]
  change WeightedFiniteCoefficient.Proof.thetaHom R.A
    (R.A.correctionTheta C.correction.Λ C.correction.G C.correction.η_id)
    (WeightedFiniteCoefficient.fieldUnit R.A _ _) = _
  rw [WeightedFiniteCoefficient.Proof.theta_associated R.A _ C.correction.theta_unit
    _ _ (D.generates _).1 (LocalFiniteSums.generator_generates C p).1
    ((D.generates _).2.trans (LocalFiniteSums.generator_generates C p).2.symm)]
  rfl

def principalEulerPrimeEquiv (R : PrincipalMellin.ActualRecipe S η) :
    LocalFiniteSums.ExteriorPrime R.A ≃ ExteriorIdealEuler.PrimeIndex R.A.cS where
  toFun p := ⟨LocalFiniteSums.primeIdeal p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, (Ideal.prime_iff_isPrime p.val.property.1).mp p.property,
    p.val.property.1⟩, p.val.property.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

theorem principal_localCorrection_eq_h_p (R : PrincipalMellin.ActualRecipe S η)
    (p : LocalFiniteSums.ExteriorPrime R.A) (s : ℂ) :
    R.localCorrection (principalEulerPrimeEquiv R p) s =
      CorrectionFactors.h_p (principalArithmeticContext R) p s := by
  unfold PrincipalMellin.ActualRecipe.localCorrection
  change Audit.Euler.principalCorrection (idealNorm p.val.asIdeal : ℂ)⁻¹
    (R.target p.val.asIdeal * comparisonRealPower (idealNorm p.val.asIdeal) (-s))
    (R.probe.coefficients.theta (R.probe.coefficients.generator
        (LocalFiniteSums.primeIdeal p)) ^ 6 *
      comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s)) = _
  rw [principal_theta_at_euler_generator]
  unfold Audit.Euler.principalCorrection CorrectionFactors.h_p LocalFiniteSums.qPower
    LocalFiniteSums.Q SArithmeticData.exteriorNorm LocalFiniteSums.primeIdeal
  have hn : 0 < idealNorm p.val.asIdeal := by
    unfold idealNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.val.ne_bot)
  have hm : comparisonRealPower (idealNorm p.val.asIdeal) (-1) =
      (idealNorm p.val.asIdeal : ℂ)⁻¹ := by
    rw [comparisonRealPower]
    have h := Complex.exp_neg ((Real.log (idealNorm p.val.asIdeal) : ℂ))
    simpa [← Complex.ofReal_exp, Real.exp_log hn] using h
  have h2 : comparisonRealPower (idealNorm p.val.asIdeal) (-2) =
      (idealNorm p.val.asIdeal : ℂ)⁻¹ ^ 2 := by
    rw [← hm, comparisonRealPower, comparisonRealPower, pow_two, ← Complex.exp_add]
    congr 1
    ring
  have he2 : (idealNorm p.val.asIdeal : ℂ)⁻¹ *
      comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s) =
      comparisonRealPower (idealNorm p.val.asIdeal) (2 - 6 * s) := by
    rw [← hm, comparisonRealPower, comparisonRealPower, comparisonRealPower,
      ← Complex.exp_add]
    congr 1
    ring
  change _ = (1 - comparisonRealPower (idealNorm p.val.asIdeal) (-2)) *
    (1 - (1 - comparisonRealPower (idealNorm p.val.asIdeal) (-1)) * R.target p.val.asIdeal *
      comparisonRealPower (idealNorm p.val.asIdeal) (-s) -
      LocalFiniteSums.vartheta (principalArithmeticContext R) p ^ 6 *
        comparisonRealPower (idealNorm p.val.asIdeal) (2 - 6 * s)) /
    ((1 - LocalFiniteSums.vartheta (principalArithmeticContext R) p ^ 6 *
        comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s)) *
      (1 - R.target p.val.asIdeal * comparisonRealPower (idealNorm p.val.asIdeal) (-s)))
  rw [h2, hm, ← he2]
  ring

theorem principal_H_eq_H_eta (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) :
    R.H s = CorrectionFactors.H_eta (principalArithmeticContext R) s := by
  unfold PrincipalMellin.ActualRecipe.H CorrectionFactors.H_eta
  rw [← (principalEulerPrimeEquiv R).tprod_eq]
  apply tprod_congr
  intro p
  exact principal_localCorrection_eq_h_p R p s

theorem principalContourCorrection_at_double_residue
    (R : PrincipalMellin.ActualRecipe S η) (ξ : ℂ)
    (hξ : (499 / 500 : ℝ) - 1 / 100000 < ξ.re) :
    principalContourCorrection R ξ 1 (1 / 6) = R.H ξ := by
  rw [principal_H_eq_H_eta]
  exact principalContourCorrection_principal_specialization R ξ hξ

theorem principal_real_weight_measurable (R : PrincipalMellin.ActualRecipe S η) : Measurable R.W.W1Hat :=
  (ProbeSheet.MellinProof.realWeight_mellin_differentiable R.probe.W1).continuous.measurable

theorem principal_real_weight_rapid_strip_decay (R : PrincipalMellin.ActualRecipe S η) (a b : ℝ) :
    comparisonRapidStripDecay R.W.W1Hat a b := by
  intro N hN
  obtain ⟨C, hC, hb⟩ :=
    ProbeSheet.MellinProof.realWeight_mellin_rapid_on_strip R.probe.W1 a b N hN
  refine ⟨C + 1, by positivity, ?_⟩
  intro s hs
  have h := hb s.re hs s.im
  have heq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))

end
end DedekindZetaZeroFree.PrincipalMellinComparison
