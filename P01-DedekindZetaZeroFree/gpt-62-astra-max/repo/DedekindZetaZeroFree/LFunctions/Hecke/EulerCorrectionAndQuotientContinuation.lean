module
public import DedekindZetaZeroFree.CharacterSums.Gauss.CompatibleCharactersAndSquarefreeReciprocity

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalInitialEulerSeparation

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField Topology
open IsDedekindDomain Filter
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private alias finite_prime_delete_hasSum := DedekindZetaZeroFree.Detector.FiniteEulerDeletion.finite_prime_delete_hasSum

private theorem norm_power (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s = comparisonRealPower q s := by apply @DedekindZetaZeroFree.NormalizedProbe.TripleMellin.TermRace.cpow_positive <;> assumption

private theorem L_eq_zeta (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 1 < s.re) : R.L s = InitialSeparatedEuler.zetaS R.A s := by
  let W := fun I => R.target I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hW0 : W ⊥ = 0 := by simp [W, (R.target.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  have hWmul (a b : Ideal (𝓞 F)) : W (a*b) = W a * W b := by
    dsimp [W]
    rw [R.target.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]; ring
  let g := fun I => if ∃ v ∈ R.A.Sf, I ≤ v.asIdeal then 0 else W I
  have hg : Function.support g ⊆ {I | I ≠ ⊥ ∧ I ⊔ R.A.cS = ⊤} := by
    intro I hI
    have hi : I ≠ ⊥ := by intro h; subst I; simpa [g, W, hW0] using hI
    refine ⟨hi, ?_⟩
    apply (R.A.exterior_iff ⟨I, hi⟩).mpr
    intro v hv
    have hn : ¬ I ≤ v.asIdeal := fun h => hI (by simp [g, show ∃ v ∈ R.A.Sf, I ≤ v.asIdeal from ⟨v,hv,h⟩])
    by_contra ht
    exact hn (by rw [(v.isMaximal.eq_of_le ht le_sup_right)]; exact le_sup_left)
  have heq (I : R.A.Exterior) : g I.val = (Ideal.absNorm I.val : ℂ)^(-s) := by
    have hn : ¬ ∃ v ∈ R.A.Sf, I.val ≤ v.asIdeal := by
      rintro ⟨v,hv,h⟩
      have := sup_le h le_rfl
      rw [((R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v hv)] at this
      exact v.isMaximal.ne_top (top_unique this)
    rw [show g I.val = W I.val by simp [g,hn]]
    dsimp [W]
    rw [R.probe.principal I.val I.property.1 ?_, one_mul]
    by_contra h
    obtain ⟨p,hp,hle⟩ := Ideal.exists_le_maximal (I.val ⊔ R.A.modulus) h
    have hmod := le_sup_right.trans hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨p,hp.isPrime,(ne_bot_of_le_ne_bot R.A.modulus_ne_zero hmod)⟩
    have := sup_le (le_sup_left.trans hle) le_rfl
    rw [((R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v
      (R.A.modulus_support v hmod))] at this
    exact hp.ne_top (top_unique this)
  have hres := ((hasSum_subtype_iff_of_support_subset hg).mpr (finite_prime_delete_hasSum F W hW0 hWmul _
    (R.continuation.series s hs) R.A.Sf)).tsum_eq.symm
  simp only [Function.comp_def] at hres
  change _ = ∑' I : R.A.Exterior, g I.val at hres
  simp_rw [heq] at hres
  convert hres using 1
  · unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    dsimp [W, idealNorm]
    rw [← norm_power (Ideal.absNorm v.asIdeal : ℝ) (by
      exact_mod_cast (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)))]
    simp
  · rfl

alias EulerCorrectionAndQuotientContinuation.L_eq_zeta := L_eq_zeta

private alias principal_coefficient_field_trace := DedekindZetaZeroFree.PrincipalMellinSource.additiveCharacter_eq_fieldTrace

private theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
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

theorem initial_continuation_agreement
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus minus : Frequency R → ℂ → ℂ)
    (hC : R.probe.correction = C.correction)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (u : Frequency R) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries R u ξ w z =
      (R.L (6 * z) * plus u w *
        AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z) / minus u ξ := by
  have h := AllRowEuler.InitialSeparation.initial_euler_quotient C R.probe.coefficients ((PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)))
    (U u) ξ w z hξ hw hz
  rw [hU u] at h
  rw [← L_eq_zeta R (6 * z) (by norm_num [Complex.mul_re, hz])] at h
  rw [← hplusSeries u w (by rw [hw]; norm_num)] at h
  rw [← hminusSeries u ξ (by rw [hξ]; norm_num)] at h
  simpa only [separatedSeries, NormalizedProbe.principalSeparatedMellinSeries,
    NormalizedProbe.separatedMellinSeries] using h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
open Filter Set Metric

set_option maxHeartbeats 1500000

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

variable (R : PrincipalMellin.ActualRecipe S η)
  (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
  (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
  (plus minus : Frequency R → ℂ → ℂ)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
