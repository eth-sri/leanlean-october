module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.FrequencyNormValuations
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped NumberField

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped NumberField
variable {F : Type} [Field F] [NumberField F]

theorem deleted_exterior_continuation_eq
    (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (H : NonprincipalRayHeckeData F ν.conductor ν.character)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (hSD : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (c : A.Exterior → ℂ)
    (hc : ∀ I : A.Exterior,
      c I = Detector.deletedPrimitiveIdealCoefficient F ν D I.val)
    (l : ℂ → ℂ) (hl : DifferentiableOn ℂ l {s : ℂ | 0 < s.re})
    (hseries : ∀ s : ℂ, 1 < s.re →
      l s = InitialSeparatedEuler.dirichletSeries c s) :
    ∀ w : ℂ, 0 < w.re →
      l w = H.L w * Detector.finiteEulerDeletionMask F D
        (fun v => ν.character v.asIdeal) w := by
  classical
  let T := {s : ℂ | 0 < s.re}
  have hT : IsOpen T := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨hmaskdiff, -, hBs⟩ :=
    Detector.deleted_primitive_L_continuation F ν D hD T H.L ((H.L_holo.analyticOnNhd hT).meromorphicOn) H.series
  let g := fun s => H.L s *
    Detector.finiteEulerDeletionMask F D (fun v => ν.character v.asIdeal) s
  have heq : ∀ s : ℂ, 1 < s.re → l s = g s := by
    intro s hs
    have hdir : InitialSeparatedEuler.dirichletSeries c s =
        ∑' I : Ideal (𝓞 F), Detector.deletedPrimitiveIdealCoefficient F ν D I *
          (Ideal.absNorm I : ℂ) ^ (-s) := by
      have hzero : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) →
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s) = 0 := by
        intro I hn
        have hc0 : Detector.deletedPrimitiveIdealCoefficient F ν D I = 0 := by
          by_cases hbot : I = ⊥
          · subst hbot
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            by_cases hex : ∃ v ∈ D, (⊥ : Ideal (𝓞 F)) ≤ v.asIdeal
            · simp [hex]
            · simp only [hex, if_false]
              exact (ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
          · have hex : ∃ v ∈ D, I ≤ v.asIdeal := by
              have hA : ¬ ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                  v ∈ A.Sf → I ⊔ v.asIdeal = ⊤ := fun hall => (fun h => hn ⟨hbot, h⟩) ((SArithmeticData.exterior_iff A ⟨I, hbot⟩).mpr hall)
              push Not at hA
              obtain ⟨v, hvS, hvv⟩ := hA
              exact ⟨v, hSD (by exact hvS), le_sup_left.trans (v.isMaximal.eq_of_le hvv le_sup_right).symm.le⟩
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            simp [hex]
        rw [hc0, zero_mul]
      have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
        intro I hI
        by_contra hn
        exact hI (hzero I hn)
      rw [InitialSeparatedEuler.dirichletSeries]
      rw [← tsum_subtype_eq_of_support_subset hsupp]
      apply tsum_congr
      intro I
      simp only [ExteriorIdealEuler.summand]
      rw [hc I]
    rw [hseries s hs, hdir, (hBs s hs).tsum_eq]
  have hEqOn : Set.EqOn l g T :=
    (hl.analyticOnNhd hT).eqOn_of_preconnected_of_eventuallyEq ((H.L_holo.mul (hmaskdiff.differentiableOn.mono (Set.subset_univ T))).analyticOnNhd hT) (convex_halfSpace_re_gt 0).isPreconnected
      (z₀ := (2 : ℂ)) (by norm_num [T])
      (by
        filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
          (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
        exact heq s hs)
  intro w hw
  simpa [g] using (hEqOn (by simpa [T] using hw))

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain UniqueFactorizationMonoid

theorem integral_kummer_conductor_cost
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (σ : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : S.integer F) (hu : u ≠ 0)
      (χ : Detector.PrimitiveFrequencyCharacter F),
      Detector.IsKummerFrequencyCharacter F ζ12 σ S
        (Units.mk0 (u : F) (by exact_mod_cast hu)) χ →
      (Ideal.absNorm χ.conductor : ℝ) ≤
        C * (Detector.frequencyNorm F S u : ℝ) := by
  classical
  obtain ⟨b, hb6, hb⟩ :=
    Detector.Conductor.LocalExponent.sextic_conductor_exponent_bounds F
  obtain ⟨C, hC, hnorm⟩ :=
    Detector.Conductor.NormFactorization.norm_le_exterior_prime_product F S hS b
  refine ⟨C, hC, ?_⟩
  intro u hu χ hχ
  have hExp := hb χ (Detector.Conductor.global_kummer_sixth_power F ζ12 hζ12 σ S hS
        (Units.mk0 (u : F) (by exact_mod_cast hu)) χ hχ)
  have hFinite : {v : HeightOneSpectrum (𝓞 F) | χ.conductor ≤ v.asIdeal}.Finite := by
    simpa only [Ideal.dvd_iff_le] using (Ideal.finite_factors χ.conductor_ne_zero)
  let T := hFinite.toFinset.filter (fun v => v ∉ S)
  have hTmem : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ T ↔ χ.conductor ≤ v.asIdeal ∧ v ∉ S := by
    intro v
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hTval : ∀ v ∈ T, v.valuation F (u : F) < 1 := by
    intro v hv
    obtain ⟨hIle, hvS⟩ := (hTmem v).mp hv
    refine lt_of_le_of_ne (u.property v hvS) ?_
    intro heq
    refine v.isPrime.ne_top (top_unique ?_)
    rw [← ((hχ v hvS (by exact heq)).1)]; exact sup_le le_rfl hIle
  have h1 : (Ideal.absNorm χ.conductor : ℝ) ≤
      C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := by
    refine hnorm χ.conductor χ.conductor_ne_zero T ?_ ?_ ?_
    · intro v _
      exact hExp v
    · intro v hvS
      have hcop : (Ideal.absNorm v.asIdeal).Coprime 6 := by
        by_contra h
        exact hvS (hSix v h)
      simpa [hb6 v hcop] using hExp v
    · intro v hvS hle
      exact (hTmem v).mpr ⟨hle, hvS⟩
  haveI : Finite ((S.integer F) ⧸ Ideal.span {u}) := (by
    obtain ⟨Sf, hSf⟩ := hS.exists_finset_coe
    subst hSf
    exact (sProductModulus_eq_principalIdeal_index F Sf u hu).1)
  have h3 : (Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) : ℝ) ≤
      (Detector.frequencyNorm F S u : ℝ) := by
    have hfn : (Detector.frequencyNorm F S u : ℝ) =
        (Nat.card ((S.integer F) ⧸ Ideal.span ({u} : Set (S.integer F))) : ℝ) := rfl
    rw [hfn]
    exact_mod_cast (Nat.card_le_card_of_surjective _
      (Ideal.Quotient.factor_surjective (Ideal.le_radical)))
  calc _
      ≤ C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := h1
    _ ≤ C * (Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) : ℝ) :=
        mul_le_mul_of_nonneg_left (Detector.Conductor.RadicalQuotient.exterior_prime_product_le_radical_index
          F S hS u hu T (fun v hv => ⟨((hTmem v).mp hv).2, hTval v hv⟩)) hC.le
    _ ≤ C * (Detector.frequencyNorm F S u : ℝ) := mul_le_mul_of_nonneg_left h3 hC.le

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]

 def rawValuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)

theorem raw_plus_inducer_isKummer
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : ∀ I : A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I =
        Detector.deletedPrimitiveIdealCoefficient F χ
          (RawHeckeRows.rawDeletionSet U) I.val) :
    Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ := by
  classical
  intro v hv huval
  simp only [Units.val_mk0] at huval

  have hexterior : v.asIdeal ⊔ A.cS = ⊤ := by
    by_contra hn
    obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp (le_sup_right.trans_eq (v.isMaximal.eq_of_le hn le_sup_left).symm)
    exact hv ((HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)) ▸ hw)
  let p : ExteriorPrime A := ⟨v, hexterior⟩
  have hIval : (primeIdeal p).val = v.asIdeal := rfl

  have hmap_extend_le : A.extendIdeal (primeIdeal p) ≤ rawValuationIdeal A v hv := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (((algebraMap (𝓞 F) A.R) a : A.R) : F) < 1
    have hcoe : (((algebraMap (𝓞 F) A.R) a : A.R) : F) = algebraMap (𝓞 F) F a := rfl
    rw [hcoe]
    exact (v.valuation_lt_one_iff_mem a).mpr (hIval ▸ ha)

  have hexp : idealPrimeExponent v.asIdeal U.ideal.val = 0 := by
    have h1 := ArithmeticContext.actual_generator_valuation A U.ideal U.u U.generates
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) rfl v hv
    simp only [Units.val_mk0] at h1
    have h2 : WithZero.exp (-(idealPrimeExponent v.asIdeal U.ideal.val : ℤ)) = 1 := by
      rw [← h1]; exact huval
    have hge :=
      WithZero.one_le_exp_iff.mp h2.ge
    have hez : (idealPrimeExponent v.asIdeal U.ideal.val : ℤ) = 0 := by omega
    exact_mod_cast hez
  have hnot : ¬ U.ideal.val ≤ v.asIdeal := by
    intro hle
    exact (Multiset.count_eq_zero.mp hexp) ((Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr
      ⟨v.isPrime, hle⟩)

  have hvD : v ∉ RawHeckeRows.rawDeletionSet U := by
    simp only [RawHeckeRows.rawDeletionSet, Set.mem_union, Set.mem_setOf_eq]
    exact fun h => h.elim hv hnot
  have hdel : Detector.deletedPrimitiveIdealCoefficient F χ
      (RawHeckeRows.rawDeletionSet U) v.asIdeal = χ.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg]
    rintro ⟨w, hw, hle⟩
    rw [((HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm)] at hw
    exact hvD hw

  have hchi : χ.character v.asIdeal = σ (A.sexticResidue (primeIdeal p) U.u) := by
    rw [← hdel, ← hIval, ← hχ (primeIdeal p)]
    exact AllRowEuler.UnitCovariance.residueCoefficient_eq (primeIdeal p) U.u

  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
    have hmax : (A.extendIdeal (primeIdeal p)).IsMaximal := by
      apply Ideal.Quotient.maximal_of_isField
      exact (A.exteriorLocalResidueEquiv (primeIdeal p) v rfl).toMulEquiv.isField
        (Field.toIsField (SArithmeticData.exteriorLocalResidue v))
    haveI := hmax
    rw [isUnit_iff_ne_zero]
    intro hz
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hlt : v.valuation F (U.u : F) < 1 := hmap_extend_le hmem
    rw [huval] at hlt
    exact lt_irrefl 1 hlt
  let q := hunit.unit
  have hqval := hunit.unit_spec
  obtain ⟨j, hj, hjchar, hjred⟩ :=
    A.sexticResidueFamily_normalized.2.1 (primeIdeal p) v hIval q

  have hchar : χ.character v.asIdeal = σ ((A.zeta12 ^ 2) ^ j) := by
    rw [hchi]
    have h1 : A.sexticResidue (primeIdeal p) U.u =
        ((A.sexticResidueFamily (primeIdeal p)) q : F) := by
      unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
      rw [← hqval, MulChar.ofUnitHom_coe]
    rw [h1, hjchar, pow_mul]
  refine ⟨?_, ⟨⟨j, hj⟩, ?_, hchar⟩⟩
  ·
    by_contra hcop
    have hz := (χ.character.eq_zero_iff' v.asIdeal).mpr (Or.inr hcop)
    rw [hchar] at hz
    exact pow_ne_zero j (pow_ne_zero 2 (A.primitive_zeta12.ne_zero (by decide))) (σ.injective (by rw [hz, map_zero]))
  ·
    have hcard : Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) = Ideal.absNorm v.asIdeal := by
      rw [A.exteriorResidue_card (primeIdeal p), hIval]
    rw [hcard] at hjred
    have hmk : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
        (U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) =
        Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
          (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) := by
      calc _
          = (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) ^
              ((Ideal.absNorm v.asIdeal - 1) / 6) := by rw [map_pow]
        _ = q ^
              ((Ideal.absNorm v.asIdeal - 1) / 6) := by rw [← hqval]
        _ = _ := hjred.symm
    have hmem : U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
        algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) ∈
        A.extendIdeal (primeIdeal p) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hmk, sub_self]
    have hval2 : v.valuation F
        ((U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
          algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) : A.R) : F) < 1 :=
      hmap_extend_le hmem
    have hcoe2 : ((U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
          algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) : A.R) : F) =
        (U.u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - (A.zeta12 ^ 2) ^ j := by
      simp only [Subalgebra.coe_sub, Subalgebra.coe_pow]
      congr 1
      push_cast
      rw [show (algebraMap (𝓞 F) F A.primitive_zeta12.toInteger) = A.zeta12 from
        A.primitive_zeta12.coe_toInteger, pow_mul]
    rw [hcoe2] at hval2
    exact hval2

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem raw_plus_inducer_conductor_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (P : Frequency R → Detector.PrimitiveFrequencyCharacter F)
    (hP : ∀ (u : Frequency R) (I : R.A.Exterior),
      AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
        Detector.deletedPrimitiveIdealCoefficient F (P u)
          (RawHeckeRows.rawDeletionSet (U u)) I.val) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency R,
      1 + (Ideal.absNorm (P u).conductor : ℝ) ≤ C * frequencyNorm R u := by
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ R.A.Sf := by
    intro v hv
    by_contra hn
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v hn)
  obtain ⟨C, hC, hcost⟩ := RawInducerArithmetic.integral_kummer_conductor_cost F
    R.A.zeta12 R.A.primitive_zeta12 R.σ _ R.A.Sf.finite_toSet hSix
  refine ⟨1 + C, by positivity, ?_⟩
  intro u
  have hbound := hcost (U u).u (U u).generates.1 (P u) (RawInducerArithmetic.raw_plus_inducer_isKummer R.A R.σ (U u) (P u) (hP u))
  have hnorm := RawInducerArithmetic.actual_frequency_norm_dictionary R u
  rw [hU u, ← hnorm.1] at hbound
  calc
    _ ≤
        frequencyNorm R u + C * frequencyNorm R u := add_le_add hnorm.2 hbound
    _ = (1 + C) * frequencyNorm R u := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound

end
