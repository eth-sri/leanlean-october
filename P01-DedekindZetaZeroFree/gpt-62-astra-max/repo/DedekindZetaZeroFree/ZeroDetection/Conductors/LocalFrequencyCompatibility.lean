module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyTwistsAndLocalCharacters
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.ExteriorResidueCharacterInjectivity

@[expose] public section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

open scoped NumberField
open NumberField IsDedekindDomain UniqueFactorizationMonoid

section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem conductor_eq_primePart_mul_away (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I = v.asIdeal ^ idealPrimeExponent v.asIdeal I * idealAwayPrimePart F v I := by
  classical
  rw [idealPrimeExponent, Multiset.pow_count, idealAwayPrimePart]
  simpa [eq_comm, prod_normalizedFactors_eq, hI, normalize_eq] using Multiset.prod_filter_mul_prod_filter_not (s := normalizedFactors I) (fun p => p = v.asIdeal)

theorem away_span_eq_of_not_mem (a : 𝓞 F) (ha : a ≠ 0)
    (hav : a ∉ v.asIdeal) :
    idealAwayPrimePart F v (Ideal.span {a}) = Ideal.span {a} := by
  classical
  have hspan : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha
  have hv : v.asIdeal ∉ normalizedFactors (Ideal.span {a}) := by
    rw [mem_normalizedFactors_iff hspan]
    rintro ⟨_, hd⟩
    exact hav (Ideal.dvd_iff_le.mp hd (Ideal.mem_span_singleton_self a))
  unfold idealAwayPrimePart
  rw [Multiset.filter_eq_self.mpr (fun p hp => by intro he; subst p; exact hv hp)]
  simpa using prod_normalizedFactors_eq hspan

theorem integral_unit_mem_higherUnits (a : 𝓞 F) (ha : a ≠ 0)
    (hav : a ∉ v.asIdeal) (k : ℕ) (hak : a - 1 ∈ v.asIdeal ^ k) :
    CRTLocalHigherUnits F v k (integralElementLocalUnit F v a ha) := by
  let b : v.adicCompletionIntegers F := algebraMap _ _ a
  have hb : IsUnit b := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (v.valuedAdicCompletion_eq_valuation' (a : F)).trans
      (v.valuation_eq_one_iff_notMem.mpr hav)
  refine ⟨hb.unit, ?_, ?_⟩
  · apply Units.ext
    change (hb.unit : v.adicCompletion F) = _
    rw [hb.unit_spec]
    rfl
  · simpa using
      (CRT_completed_power_mem_iff F v (a - 1) k).mpr hak

end

section

variable (F : Type) [Field F] [NumberField F]

theorem frequency_local_component_nontrivial_below_conductor
    (omega : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (delta : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hlocal : IsFrequencyLocalComponent F omega v delta)
    (k : ℕ) (hk : k < idealPrimeExponent v.asIdeal omega.conductor) :
    ∃ x : (v.adicCompletion F)ˣ,
      CRTLocalHigherUnits F v k x ∧ delta x ≠ 1 := by
  classical
  let e := idealPrimeExponent v.asIdeal omega.conductor
  let q := idealAwayPrimePart F v omega.conductor
  have hfactor :=
    conductor_eq_primePart_mul_away F v _ omega.conductor_ne_zero
  have hle : omega.conductor ≤ v.asIdeal ^ k * q := by
    rw [hfactor]
    simpa only [mul_comm] using
      mul_le_mul_right (Ideal.pow_le_pow_right (I := v.asIdeal) hk.le) q
  have hlt : omega.conductor < v.asIdeal ^ k * q := by
    apply lt_of_le_of_ne hle
    intro heq
    have hek : e = k := by simpa [v.irreducible.normalizedFactors_pow] using (congrArg (fun I : Ideal (𝓞 F) => (normalizedFactors I).count v.asIdeal) (mul_right_cancel₀ (prod_ne_zero_of_subset_normalizedFactors (Multiset.filter_subset _ _)) (hfactor.symm.trans heq)))
    omega
  obtain ⟨a, ha, hacong, _, hacop, hane⟩ := omega.primitive _ hlt
  have hav : a ∉ v.asIdeal := by
    intro hav
    have hspan : Ideal.span {a} ≤ v.asIdeal := Ideal.span_le.mpr (by simpa using hav)
    exact v.isPrime.ne_top (top_unique ((hacop ▸ sup_le hspan (by
      rw [hfactor]
      exact Ideal.mul_le_left.trans (Ideal.pow_le_self (by omega)))) : ⊤ ≤ v.asIdeal))
  refine ⟨integralElementLocalUnit F v a ha,
    integral_unit_mem_higherUnits F v a ha hav k (Ideal.mul_le_left hacong), ?_⟩
  intro heq
  have hval := hlocal a ha (Ideal.mul_le_right hacong)
  rw [away_span_eq_of_not_mem F v a ha hav] at hval
  have hone : omega.character (Ideal.span {a}) = 1 := by
    have hi : (omega.character (Ideal.span {a}))⁻¹ = 1 := by
      rw [← hval, heq]
      rfl
    simpa only [inv_eq_one] using hi
  exact hane hone

private theorem positive_representative
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (a : 𝓞 F) :
    ∃ b : 𝓞 F, b - a ∈ m ∧ ∀ φ : F →+* ℝ, 0 < φ (b : F) := by
  have hn := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm)
  have hb : ∃ B : ℝ, ∀ φ : F →+* ℝ, -φ (a : F) < B := ⟨∑ φ : F →+* ℝ, |φ (a : F)| + 1, fun φ => by
      have ht := Finset.single_le_sum (fun i _ =>
        abs_nonneg (i (a : F))) (Finset.mem_univ φ)
      linarith [neg_le_abs (φ (a : F))]⟩
  obtain ⟨B, hB⟩ := hb
  obtain ⟨n, hnB⟩ := exists_nat_gt B
  let b := a + (n * Ideal.absNorm m : ℕ)
  have hp (φ : F →+* ℝ) : 0 < φ (b : F) := by
    have hN : (1 : ℝ) ≤ Ideal.absNorm m := by exact_mod_cast hn
    have hnb : (n : ℝ) ≤ (n : ℝ) * Ideal.absNorm m := by
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    change 0 < (φ.comp (algebraMap (𝓞 F) F)) (a + (n * Ideal.absNorm m : ℕ))
    rw [map_add, map_natCast]
    simp only [Nat.cast_mul, RingHom.comp_apply]
    linarith [hB φ]
  refine ⟨b, ?_, hp⟩
  simpa [b] using (by
    simpa using m.mul_mem_left n m.absNorm_mem)

end

alias LocalFrequencyCompatibility.positive_representative := positive_representative

private alias completed_power_criterion := DedekindZetaZeroFree.PrimitiveCharactersByCRT.CRT_power_criterion

set_option maxHeartbeats 800000 in

theorem higherUnits_mem_closure_positive_congruence
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (x : (v.adicCompletion F)ˣ)
    (hx : CRTLocalHigherUnits F v (idealPrimeExponent v.asIdeal f) x) :
    x ∈ closure {u : (v.adicCompletion F)ˣ | ∃ (a : 𝓞 F) (ha : a ≠ 0),
      a - 1 ∈ f ∧ (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
      a ∉ v.asIdeal ∧ u = integralElementLocalUnit F v a ha} := by
  let algebraMap₀ := algebraMap (𝓞 F) (v.adicCompletion F)
  classical
  let e := idealPrimeExponent v.asIdeal f
  let q := idealAwayPrimePart F v f
  have hq0 : q ≠ 0 := prod_ne_zero_of_subset_normalizedFactors (Multiset.filter_subset _ _)
  have hcop : v.asIdeal ^ e ⊔ q = ⊤ := Ideal.pow_sup_eq_top
    (Conductor.LocalCertification.idealAwayPrimePart_coprime F v f)
  have hfactor : f = v.asIdeal ^ e * q := conductor_eq_primePart_mul_away F v f hf
  obtain ⟨b, rfl, hb⟩ := hx
  rw [Units.isEmbedding_val₀.closure_eq_preimage_closure_image]
  change (b : v.adicCompletion F) ∈ closure (Units.val ''
    {u : (v.adicCompletion F)ˣ | ∃ (a : 𝓞 F) (ha : a ≠ 0),
      a - 1 ∈ f ∧ (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
      a ∉ v.asIdeal ∧ u = integralElementLocalUnit F v a ha})
  rw [mem_closure_iff_nhds']
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom γ
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  have hp' : Valued.v (algebraMap₀ p) = WithZero.exp (-1) :=
    (v.valuedAdicCompletion_eq_valuation p).trans ((v.valuation_of_algebraMap p).trans hp)
  obtain ⟨N, hN⟩ := Valued.exists_pow_lt_of_le_exp_neg_one hp'.le γ'
  let n := max N (e + 1)
  have hnN : N ≤ n := le_max_left _ _
  have hen : e ≤ n := by dsimp [n]; omega
  have hn0 : n ≠ 0 := by dsimp [n]; omega
  have hsmall : WithZero.exp (-(n : ℤ)) < (γ' : WithZero (Multiplicative ℤ)) := by
    apply lt_of_le_of_lt _ hN
    rw [hp', ← WithZero.exp_nsmul]
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    rw [WithZero.exp_le_exp]
    omega
  obtain ⟨c, hc⟩ := CRT_completed_residue_representative F v (b : v.adicCompletionIntegers F) n
  obtain ⟨d, hdc, hdq⟩ := Conductor.LocalCertification.exists_integral_away_congruent F v f n c
  have hmod0 : v.asIdeal ^ n * q ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) hq0
  obtain ⟨a, had, hpos⟩ := positive_representative F (v.asIdeal ^ n * q) hmod0 d
  have hac : a - c ∈ v.asIdeal ^ n := by
    convert (v.asIdeal ^ n).add_mem (Ideal.mul_le_left had) hdc using 1 <;> ring
  have haq : a - 1 ∈ q := by
    convert q.add_mem (Ideal.mul_le_right had) hdq using 1 <;> ring
  have hab : algebraMap (𝓞 F) (v.adicCompletionIntegers F) a - b ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
    have hac' := (CRT_completed_power_mem_iff F v (a - c) n).mpr hac
    simp only [map_sub] at hac'
    convert (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n).add_mem hac' hc using 1 <;> ring
  have haunit := CRT_congruent_isUnit F v n hn0 _ b hab
  have hav : a ∉ v.asIdeal := by
    have hval : Valued.v (algebraMap₀ a) = 1 :=
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (R := 𝓞 F) (K := F) (v := v) (a := algebraMap _ _ a)).mp haunit
    apply (v.valuation_eq_one_iff_notMem (K := F)).mp
    change v.valuation F (a : F) = 1
    exact (v.valuedAdicCompletion_eq_valuation' (K := F) (a : F)).symm.trans hval
  have ha : a ≠ 0 := by intro h; exact hav (h ▸ v.asIdeal.zero_mem)
  have haf : a - 1 ∈ f := by
    rw [hfactor, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hcop)]
    refine ⟨?_, haq⟩
    apply (CRT_completed_power_mem_iff F v (a - 1) e).mp
    have hab' := Ideal.pow_le_pow_right hen hab
    convert (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ e).add_mem hab' hb using 1 <;>
      simp only [map_sub, map_one] <;> ring
  have has : algebraMap₀ a ∈ s := by
    apply hγ
    apply Valued.v.restrict_lt_iff_lt_embedding.mpr
    change Valued.v (algebraMap₀ a - (b : v.adicCompletion F)) < _
    exact ((completed_power_criterion F v _ n).mp hab).trans_lt hsmall
  refine ⟨⟨algebraMap₀ a, ?_⟩, has⟩
  exact ⟨integralElementLocalUnit F v a ha, ⟨a, ha, haf, hpos, hav, rfl⟩, rfl⟩

variable (F : Type) [Field F] [NumberField F]

theorem frequency_local_component_trivial_on_conductor
    (omega : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (delta : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hlocal : IsFrequencyLocalComponent F omega v delta)
    (x : (v.adicCompletion F)ˣ)
    (hx : CRTLocalHigherUnits F v (idealPrimeExponent v.asIdeal omega.conductor) x) :
    delta x = 1 := by
  have heq : Set.EqOn delta (fun _ => 1) ({u | ∃ (a : 𝓞 F) (ha : a ≠ 0),
    a - 1 ∈ omega.conductor ∧ (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
    a ∉ v.asIdeal ∧ u = integralElementLocalUnit F v a ha}) := by
    rintro u ⟨a, ha, hacong, hpos, hav, rfl⟩
    apply Units.ext
    have hacong' : a - 1 ∈ idealAwayPrimePart F v omega.conductor := by
      rw [(conductor_eq_primePart_mul_away F v omega.conductor omega.conductor_ne_zero)] at hacong
      exact Ideal.mul_le_right hacong
    rw [hlocal a ha hacong', away_span_eq_of_not_mem F v a ha hav,
      omega.character.map_span' a ha hacong hpos, inv_one]
    rfl
  exact heq.closure delta.continuous continuous_const
    (higherUnits_mem_closure_positive_congruence F v omega.conductor omega.conductor_ne_zero x hx)

private theorem exponent_zero_of_coprime
    (v : HeightOneSpectrum (𝓞 F)) (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (hcop : v.asIdeal ⊔ f = ⊤) : idealPrimeExponent v.asIdeal f = 0 := by
  classical
  rw [idealPrimeExponent, Multiset.count_eq_zero, mem_normalizedFactors_iff hf]
  rintro ⟨_, hd⟩
  exact v.isPrime.ne_top ((sup_eq_left.mpr (Ideal.dvd_iff_le.mp hd)).symm.trans hcop)

private theorem higherUnits_zero_of_norm_one
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (hx : ‖(x : v.adicCompletion F)‖ = 1) : CRTLocalHigherUnits F v 0 x := by
  have hv :=
    Valued.toNormedField.norm_eq_one_iff.mp hx
  let a : v.adicCompletionIntegers F := ⟨x,
    (v.mem_adicCompletionIntegers _ F).mpr hv.le⟩
  have ha : IsUnit a :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := F) (v := v) (a := a)).mpr hv
  rw [CRTLocalHigherUnits_zero_iff]
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  change (ha.unit : v.adicCompletion F) = _
  rw [ha.unit_spec]

theorem frequency_local_component_uniformizer
    (omega : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (delta : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hlocal : IsFrequencyLocalComponent F omega v delta)
    (hcop : v.asIdeal ⊔ omega.conductor = ⊤)
    (pi : (v.adicCompletion F)ˣ)
    (hpi : ‖(pi : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :
    omega.character v.asIdeal = (delta pi : ℂ) := by
  classical
  have he :=
    exponent_zero_of_coprime F v _ omega.conductor_ne_zero hcop
  have hfaway : idealAwayPrimePart F v omega.conductor = omega.conductor := by
    simpa only [he, pow_zero, one_mul] using (conductor_eq_primePart_mul_away F v omega.conductor omega.conductor_ne_zero).symm
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  obtain ⟨d, hdp, hdf⟩ := Conductor.LocalCertification.exists_integral_away_congruent
    F v omega.conductor 2 p
  rw [show Conductor.Raw.idealAwayPrimePart F v omega.conductor = omega.conductor from hfaway] at hdf
  obtain ⟨a, had, hpos⟩ := positive_representative F (v.asIdeal ^ 2 * omega.conductor) (mul_ne_zero (pow_ne_zero _ v.ne_bot) omega.conductor_ne_zero) d
  have haf : a - 1 ∈ omega.conductor := by
    convert omega.conductor.add_mem (Ideal.mul_le_right had) hdf using 1 <;> ring
  have haVal : v.intValuation a = WithZero.exp (-1) := by
    apply (v.intValuation.map_eq_of_sub_lt ?_).trans hp
    apply lt_of_le_of_lt ((v.intValuation_le_pow_iff_mem (a - p) 2).mpr (by
      convert (v.asIdeal ^ 2).add_mem (Ideal.mul_le_left had) hdp using 1 <;> ring))
    rw [hp, WithZero.exp_lt_exp]
    norm_num
  have ha : a ≠ 0 := by
    intro hz
    have hn : WithZero.exp (-1) ≠ (0 : WithZero (Multiplicative ℤ)) := WithZero.coe_ne_zero
    exact hn (by simpa [hz] using haVal.symm)
  have hspan0 : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha
  have hae : idealPrimeExponent v.asIdeal (Ideal.span {a}) = 1 := by
    have hval := v.intValuation_eq_exp_neg_multiplicity ha
    rw [haVal, WithZero.exp_inj, neg_inj] at hval
    rw [idealPrimeExponent, v.count_normalizedFactors_eq_multiplicity hspan0]
    omega
  let u := integralElementLocalUnit F v a ha
  have hunorm : ‖(u : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    change ‖FinitePlace.embedding v (a : F)‖ = _
    rw [FinitePlace.norm_embedding']
    rw [((v.valuation_of_algebraMap a).trans haVal)]
    simp [WithZeroMulInt.toNNReal]
  have heqdelta : delta (pi / u) = 1 := by
    apply frequency_local_component_trivial_on_conductor F omega v delta hlocal
    rw [he]
    apply higherUnits_zero_of_norm_one F v
    rw [Units.val_div_eq_div_val, norm_div, hpi, hunorm]
    apply div_self
    exact inv_ne_zero (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hdelta : delta pi = delta u := by
    rw [map_div] at heqdelta
    exact div_eq_one.mp heqdelta
  rw [hdelta]
  have hprincipal := omega.character.map_span' a ha haf hpos
  have hfactor := conductor_eq_primePart_mul_away F v (Ideal.span {a}) hspan0
  simp [hae] at hfactor
  rw [hfactor, omega.character.map_mul'] at hprincipal
  exact (eq_inv_of_mul_eq_one_left hprincipal).trans (hlocal a ha (by
    rw [hfaway]
    exact haf)).symm

theorem sprime_compatibility_of_frequency_local_components (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧
          IsFrequencyLocalComponent F omega v.val delta) :
    FixedSInjectivity.SPrimeCompatibility A omega.conductor omega.character sigma := by
  intro v
  obtain ⟨delta, hdelta, hcomp⟩ := hlocal v
  constructor
  · intro x hx
    rw [← hdelta]
    apply frequency_local_component_trivial_on_conductor <;> assumption
  constructor
  · intro k hk
    obtain ⟨x, hx, hne⟩ :=
      frequency_local_component_nontrivial_below_conductor F omega v.val delta hcomp k hk
    refine ⟨x, hx, ?_⟩
    rw [← hdelta]
    exact hne
  · intro hcop pi hpi
    rw [← hdelta]
    apply frequency_local_component_uniformizer <;> assumption

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter
