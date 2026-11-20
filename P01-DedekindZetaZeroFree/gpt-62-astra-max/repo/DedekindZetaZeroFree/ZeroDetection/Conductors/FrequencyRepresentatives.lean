module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FrequencyNormValuations

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private alias order_mul_local := DedekindZetaZeroFree.ThetaBranch.ord_mul

private alias order_pow_local := DedekindZetaZeroFree.ThetaBranch.ExteriorFrequencyBranchCoordinates.pow_order

private theorem order_eq_exp (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fˣ) (e : ℤ) :
    ThetaBranch.order p x = e ↔ p.valuation F (x : F) = WithZero.exp (-e) := by
  have hn : p.valuation F (x : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  constructor
  · intro h
    have hl : WithZero.log (p.valuation F (x : F)) = -e := by
      simpa only [ThetaBranch.order, neg_neg] using (congrArg Neg.neg h)
    rw [← WithZero.exp_log hn, hl]
  · intro h
    simp only [ThetaBranch.order, h, WithZero.log_exp, neg_neg]

private theorem order_sunit_eq_zero (A : SArithmeticData F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (u : A.U) :
    ThetaBranch.order v u.val = 0 := by
  rw [ThetaBranch.order, u.property v hv, WithZero.log_one, neg_zero]

section

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (g : Fˣ)

private theorem order_nonneg_of_le_one (h : v.valuation F (g : F) ≤ 1) : 0 ≤ ThetaBranch.order v g := by
  rw [ThetaBranch.order, neg_nonneg]
  exact (WithZero.log_le_iff_le_exp ((Valuation.ne_zero_iff _).mpr g.ne_zero)).mpr (by simpa [WithZero.exp_zero] using h)

private theorem valuation_eq_one_of_order_zero (h : ThetaBranch.order v g = 0) : v.valuation F (g : F) = 1 := by
  have := (order_eq_exp v g 0).mp h
  simpa [WithZero.exp_zero] using this

end

variable (R : PrincipalMellin.ActualRecipe S η)

private theorem rowUnit_represents (x : Fˣ)
    (hx : Detector.sixthPowerFreeFrequency F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) x) :
    ∃! u : Frequency R, Detector.frequencyEquivalent F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) x
        (ThetaReflectionData.rowUnit R.A u.val) := by
  classical
  let A := R.A
  have hxmem : (x : F) ∈ A.R := hx.1
  let hrow : ThetaReflectionData.Row A :=
    ⟨⟨(x : F), hxmem⟩, by
      intro h
      exact x.ne_zero (Subtype.ext_iff.mp h)⟩
  have hrowunit : ThetaReflectionData.rowUnit A hrow = x := Units.ext rfl
  obtain ⟨⟨u0, I⟩, hpres, huniq⟩ := R.probe.frequencies.factorization hrow
  obtain ⟨γ, hγ⟩ := hpres
  have hxeq : x = ThetaReflectionData.rowUnit A u0.val *
      R.probe.allowed.generator I ^ 6 * γ.val ^ 6 := by
    rw [← hrowunit, hγ]
  have hgenU : R.probe.allowed.generator I ∈ A.U := by
    intro v hv
    refine valuation_eq_one_of_order_zero v _ ?_
    have hgen0 : 0 ≤ ThetaBranch.order v (R.probe.allowed.generator I) := by
      obtain ⟨r, hgen, hgenF⟩ := R.probe.allowed.generates I
      refine order_nonneg_of_le_one v _ ?_
      rw [hgenF]
      exact Set.integer_valuation_le_one
        (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) F r hv
    have hxord : 0 ≤ ThetaBranch.order v x ∧ ThetaBranch.order v x < 6 := by
      obtain ⟨e, he⟩ := hx.2 v hv
      have hxe : ThetaBranch.order v x = (e.val : ℤ) := (order_eq_exp v x (e.val : ℤ)).mpr he
      constructor
      · rw [hxe]; exact Int.natCast_nonneg _
      · rw [hxe]; exact_mod_cast e.isLt
    have huord : 0 ≤ ThetaBranch.order v (ThetaReflectionData.rowUnit A u0.val) ∧
        ThetaBranch.order v (ThetaReflectionData.rowUnit A u0.val) < 6 :=
      R.probe.frequencies.sixthFree u0.val u0.property ⟨v, hv⟩
    have hrel : ThetaBranch.order v x =
        ThetaBranch.order v (ThetaReflectionData.rowUnit A u0.val) +
          6 * ThetaBranch.order v (R.probe.allowed.generator I) := by
      conv_lhs => rw [hxeq]
      rw [order_mul_local, order_mul_local, order_pow_local, order_pow_local,
        order_sunit_eq_zero A v hv γ]
      ring
    have h6eq : 6 * ThetaBranch.order v (R.probe.allowed.generator I) =
        ThetaBranch.order v x - ThetaBranch.order v (ThetaReflectionData.rowUnit A u0.val) := by
      linarith [hrel]
    omega
  have hequiv : Detector.frequencyEquivalent F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) x
        (ThetaReflectionData.rowUnit A u0.val) := by
    change x / ThetaReflectionData.rowUnit A u0.val ∈
      ((R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F).map (powMonoidHom 6)
    refine ⟨R.probe.allowed.generator I * γ.val, ?_, ?_⟩
    · exact A.U.mul_mem hgenU γ.property
    · change (R.probe.allowed.generator I * γ.val) ^ 6 =
        x / ThetaReflectionData.rowUnit A u0.val
      rw [hxeq, mul_pow, mul_assoc, mul_div_cancel_left]
  refine ⟨u0, hequiv, ?_⟩
  intro y hy
  obtain ⟨s, hs, hsy⟩ := hy
  have hgenS : s / R.probe.allowed.generator I ∈ A.U := A.U.div_mem hs hgenU
  have hyx : x = ThetaReflectionData.rowUnit A y.val * s ^ 6 := by
    have hsy' : s ^ 6 = x / ThetaReflectionData.rowUnit A y.val := hsy
    have h2 : ThetaReflectionData.rowUnit A y.val * s ^ 6 = x := by
      rw [hsy', mul_div_cancel]
    exact h2.symm
  have hpres' : ∃ γ' : A.U, ThetaReflectionData.rowUnit A hrow =
      ThetaReflectionData.rowUnit A y.val *
        R.probe.allowed.generator I ^ 6 * γ'.val ^ 6 := by
    refine ⟨⟨s / R.probe.allowed.generator I, hgenS⟩, ?_⟩
    rw [hrowunit, hyx, div_pow, mul_assoc, mul_div_cancel]
  have hpair := huniq (y, I) hpres'
  exact congrArg Prod.fst hpair

theorem actual_detector_frequency_representatives :
    ∃ (V : Detector.FrequencyRepresentatives F
        (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) ))
      (e : Frequency R ≃ V.carrier),
      (∀ u : Frequency R, (e u).val = ThetaReflectionData.rowUnit R.A u.val) ∧
      ∀ u : Frequency R,
        (Detector.frequencySNorm F
          (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) V (e u) : ℝ) =
            frequencyNorm R u := by
  let Set₀ := Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))
  classical
  let φ : Frequency R → Fˣ := fun u => ThetaReflectionData.rowUnit R.A u.val
  have hφinj : Function.Injective φ := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun z : Fˣ => (z : F)) huv
    simpa [φ, ThetaReflectionData.rowUnit] using h
  let V : Detector.FrequencyRepresentatives F
      (R.A.Sf : Set₀) :=
    { carrier := Set.range φ
      one_mem := ⟨principalFrequency R, by
        apply Units.ext
        simp [φ, principalFrequency, ThetaReflectionData.rowUnit]⟩
      power_free := by
        rintro u ⟨u', rfl⟩
        refine ⟨u'.val.val.property, ?_⟩
        intro v hv
        have hfree := R.probe.frequencies.sixthFree u'.val u'.property ⟨v, hv⟩
        have h0 := hfree.1
        have h6 : ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u'.val) < 6 := hfree.2
        refine ⟨⟨(ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u'.val)).toNat, by omega⟩, ?_⟩
        rw [(Int.toNat_of_nonneg h0)]
        exact (order_eq_exp v (ThetaReflectionData.rowUnit R.A u'.val)
          (ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u'.val))).mp rfl
      represents := by
        intro x hx
        obtain ⟨u0, hP, huniq⟩ := rowUnit_represents R x hx
        refine ⟨⟨φ u0, ⟨u0, rfl⟩⟩, hP, ?_⟩
        intro v hv
        obtain ⟨v', hv'⟩ := v.property
        exact Subtype.ext (hv'.symm.trans (congrArg φ (huniq v' (by simpa [φ, hv'] using hv)))) }
  have hVc : V.carrier = Set.range φ := rfl
  have hmem : ∀ u : Frequency R, φ u ∈ V.carrier := fun u => by
    rw [hVc]; exact ⟨u, rfl⟩
  let ψfun : Frequency R → V.carrier := fun u => ⟨φ u, hmem u⟩
  have hψinj : Function.Injective ψfun := fun u v huv => hφinj (Subtype.ext_iff.mp huv)
  have hψsurj : Function.Surjective ψfun := by
    intro v
    have hv : v.val ∈ Set.range φ := by rw [← hVc]; exact v.property
    obtain ⟨a, ha⟩ := hv
    exact ⟨a, Subtype.ext ha⟩
  refine ⟨V, Equiv.ofBijective ψfun ⟨hψinj, hψsurj⟩, ?_, ?_⟩
  · intro u
    rfl
  · intro u
    have hdict :=
      RightBound.ConductorEstimate.RawInducerArithmetic.actual_frequency_norm_dictionary
        R u
    have hS : Detector.frequencySInteger F
        (R.A.Sf : Set₀) V
          (Equiv.ofBijective ψfun ⟨hψinj, hψsurj⟩ u) = u.val.val := by
      apply Subtype.ext
      simp [Detector.frequencySInteger, ψfun, φ, ThetaReflectionData.rowUnit]
    have hnorm1 : Detector.frequencySNorm F
        (R.A.Sf : Set₀) V
          (Equiv.ofBijective ψfun ⟨hψinj, hψsurj⟩ u)
        = Detector.frequencyNorm F
          (R.A.Sf : Set₀) u.val.val := by
      simp only [Detector.frequencySNorm, Detector.frequencyNorm]
      rw [hS]
    rw [hnorm1]
    exact hdict.1.symm

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
