module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinSource
open scoped NumberField Classical
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]

private theorem support_symbol_eq_residue (A : SArithmeticData F)
    (G : ThetaBranch.AllowedRecipe A) (σ : F →+* ℂ)
    (d c : A.Exterior) (hd : Squarefree d.val)
    (r : A.R) (hr : (G.generator c : F) = (r : F)) :
    ThetaPhaseSeparation.idealSymbol A σ d (G.generator c) = σ (A.sexticResidue d r) := by
  have hr0 : r ≠ 0 := fun h => (G.generator c).ne_zero (hr.trans (by simp [h]))
  have he : ThetaReflectionData.rowUnit A ⟨r, hr0⟩ = G.generator c := Units.ext hr.symm
  have hchar : A.sexticResiduePowerChar σ d 1
      (Ideal.Quotient.mk (A.extendIdeal d) r) = σ (A.sexticResidue d r) := by
    simp only [SArithmeticData.sexticResiduePowerChar,
      show SArithmeticData.sexticExponent (1 : ℤ) = 1 from by decide, pow_one]
    by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal d) r)
    · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily d) _)
      rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
      rfl
    · rw [MulChar.map_nonunit _ hx]
      change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily d) _)
      rw [MulChar.map_nonunit _ hx, map_zero]
  have h := (NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar A σ d r).trans hchar
  rw [NormalizedProbe.exteriorSexticRowCharacter, dif_neg hr0, he] at h
  rw [← h]
  unfold ThetaPhaseSeparation.idealSymbol
  apply Finset.prod_congr rfl
  intro p hp
  have hexp : idealPrimeExponent p.val.asIdeal d.val = 1 := by
    apply Multiset.count_eq_one_of_mem
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors d.property.1).mp hd)
    simpa only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport,
      Multiset.mem_toFinset] using p.property
  rw [hexp, pow_one]
  rfl

theorem squarefree_source_generator_reciprocity
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (d c : R.A.Exterior) (hd : Squarefree d.val) (hc : Squarefree c.val)
    (hcop : d.val ⊔ c.val = ⊤) :
    ThetaPhaseSeparation.idealSymbol R.A R.σ d (R.probe.allowed.generator c) =
      ThetaPhaseSeparation.idealSymbol R.A R.σ c (R.probe.allowed.generator d) := by
  obtain ⟨a, ha, hea⟩ := R.probe.allowed.generates d
  obtain ⟨b, hb, heb⟩ := R.probe.allowed.generates c
  rw [support_symbol_eq_residue R.A R.probe.allowed R.σ d c hd b heb,
    support_symbol_eq_residue R.A R.probe.allowed R.σ c d hc a hea]
  apply congrArg R.σ
  refine (ArithmeticContext.actual_hilbert_sextic_reciprocity R.A
    R.probe.correction.H R.probe.correction.B R.probe.correction.H_actual
    R.probe.correction.B_complement).1 d c a b
      (R.probe.allowed.generator d) (R.probe.allowed.generator c)
      ha hb hea heb ?_ ?_ hcop
  · rw [← R.probe.sameComplement]
    exact R.probe.allowed.allowed d
  · rw [← R.probe.sameComplement]
    exact R.probe.allowed.allowed c

end DedekindZetaZeroFree.PrincipalMellinSource

end

section

namespace DedekindZetaZeroFree.PrincipalMellinSource

open scoped NumberField Classical
open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

private alias archPhase_eq_trace := DedekindZetaZeroFree.CodifferentResidueSieve.archPhase_eq_trace

private theorem phase_eq_eS (A : SArithmeticData F) (y : SLocalProduct F A.Sf) :
    ProbeAdditive.phase F A.Sf (fun v => ResidueTrace.localTraceCharacter v.val) y =
      (A.eS y : ℂ) := by
  have key : (A.eS y : ℂ) = (∏ w, (archTraceCharacter w (y.1 w) : ℂ)) *
      ∏ v : A.Sf, (ResidueTrace.localTraceCharacter v.val (y.2 v) : ℂ) := by
    change Circle.coeHom (A.eS y) = _
    rw [SArithmeticData.eS, AddChar.coe_mk, map_mul, map_prod, map_prod]
    rfl
  rw [ProbeAdditive.phase, archPhase_eq_trace A, key]

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

theorem additiveCharacter_eq_eS (x : F) :
    R.probe.coefficients.additiveCharacter x =
      (R.A.eS (sLocalDiagonal F R.A.Sf x) : ℂ) := by
  rw [R.probe.sameTrace]
  rw [(funext fun v => NormalizedProbe.PrincipalData.finiteTrace_eq_localTraceCharacter
    R.A R.σ R.target R.traceBad R.probe v)]
  exact phase_eq_eS R.A _

theorem additiveCharacter_eq_fieldTrace (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [additiveCharacter_eq_eS R x]
  rfl

def SourceCharacterCompatibility
    (ψ : ∀ p : ThetaBranch.ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : R.A.UnitQuotient → Fˣ →* ℂ) : Prop :=
  (∀ (p : ThetaBranch.ExteriorPrime R.A) (t : 𝓞 F),
    ψ p (Ideal.Quotient.mk p.val.asIdeal t) =
      R.probe.coefficients.additiveCharacter
        ((t : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F))) ∧
  ∀ (ε : R.A.U) (x : Fˣ),
    L (QuotientGroup.mk ε) x =
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
        R.probe.correction.η_id (R.A.diagonal x) : ℂ) *
      R.σ ((R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal x) : Fˣ) : F)

 noncomputable def representativeSourceCharacter (ε : R.A.U) : Fˣ →* ℂ where
  toFun x :=
    (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
      R.probe.correction.η_id (R.A.diagonal x) : ℂ) *
      R.σ ((R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal x) : Fˣ) : F)
  map_mul' x y := by
    have hLS : R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
        R.probe.correction.η_id (R.A.diagonal (x * y)) =
        R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
          R.probe.correction.η_id (R.A.diagonal x) *
        R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
          R.probe.correction.η_id (R.A.diagonal y) := by
      simp only [map_mul, SArithmeticData.correctionLS, SArithmeticData.ideleSInverseProduct,
        Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, mul_inv,
        Finset.prod_mul_distrib]
      ac_rfl
    rw [hLS]
    simp only [map_mul, Circle.coe_mul, R.A.H_S_mul_right,
      Subgroup.coe_mul, Units.val_mul]
    ring
  map_one' := by
    have hH : R.A.H_S (R.A.diagonal ε.val) 1 = 1 := by
      exact mul_left_cancel (show R.A.H_S (R.A.diagonal ε.val) 1 *
        R.A.H_S (R.A.diagonal ε.val) 1 = R.A.H_S (R.A.diagonal ε.val) 1 * 1 by
          simpa using (R.A.H_S_mul_right (R.A.diagonal ε.val) 1 1).symm)
    simp [SArithmeticData.correctionLS, SArithmeticData.ideleSInverseProduct, hH]

private theorem representativeSourceCharacter_eq (ε δ : R.A.U)
    (h : (QuotientGroup.mk ε : R.A.UnitQuotient) = QuotientGroup.mk δ) :
    representativeSourceCharacter R ε = representativeSourceCharacter R δ := by
  have hc := congrArg R.A.unitQuotientClass h
  change R.A.sClass ε.val = R.A.sClass δ.val at hc
  apply MonoidHom.ext
  intro x
  change _ * R.σ ((R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal x) : Fˣ) : F) =
    _ * R.σ ((R.A.H_S (R.A.diagonal δ.val) (R.A.diagonal x) : Fˣ) : F)
  rw [← R.probe.correction.H_actual, ← R.probe.correction.H_actual]
  change _ * R.σ (R.probe.correction.H (R.A.sClass ε.val) _ : F) =
    _ * R.σ (R.probe.correction.H (R.A.sClass δ.val) _ : F)
  rw [hc]

theorem exists_rational_source_characters :
    ∃ L : R.A.UnitQuotient → Fˣ →* ℂ,
      (∀ v x, ‖L v x‖ = 1) ∧
      ∀ (ε : R.A.U) (x : Fˣ),
        L (QuotientGroup.mk ε) x =
          (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
            R.probe.correction.η_id (R.A.diagonal x) : ℂ) *
            R.σ ((R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal x) : Fˣ) : F) := by
  classical
  let rep := fun v =>
    Classical.choose (QuotientGroup.mk'_surjective R.A.unitSixthPowers v)
  have hrep (v : R.A.UnitQuotient) : (QuotientGroup.mk (rep v) : R.A.UnitQuotient) = v :=
    Classical.choose_spec (QuotientGroup.mk'_surjective R.A.unitSixthPowers v)
  refine ⟨fun v => representativeSourceCharacter R (rep v), ?_, ?_⟩
  · intro v x
    have hp : R.σ ((R.A.H_S (R.A.diagonal (rep v).val)
        (R.A.diagonal x) : Fˣ) : F) ^ 6 = 1 := by
      rw [← map_pow]
      simpa using
        congrArg (fun u : Fˣ => R.σ (u : F)) ((R.A.H_S (R.A.diagonal (rep v).val) (R.A.diagonal x)).property)
    have hn : ‖R.σ ((R.A.H_S (R.A.diagonal (rep v).val)
        (R.A.diagonal x) : Fˣ) : F)‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
      rw [← norm_pow, hp, norm_one]
    change ‖_ * R.σ ((R.A.H_S (R.A.diagonal (rep v).val)
      (R.A.diagonal x) : Fˣ) : F)‖ = 1
    rw [norm_mul, Circle.norm_coe, hn, mul_one]
  · intro ε x
    exact (DFunLike.congr_fun
      (representativeSourceCharacter_eq R (rep (QuotientGroup.mk ε)) ε (hrep _)) x)

theorem exists_primitive_source_characters :
    ∃ ψ : ∀ p : ThetaBranch.ExteriorPrime R.A,
        AddChar (DHCubic.Residue F p.val) ℂ,
      (∀ p, (ψ p).IsPrimitive) ∧
      ∀ (p : ThetaBranch.ExteriorPrime R.A) (t : 𝓞 F),
        ψ p (Ideal.Quotient.mk p.val.asIdeal t) =
          R.probe.coefficients.additiveCharacter
            ((t : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) := by
  classical
  have hp (p : ThetaBranch.ExteriorPrime R.A) :
      ∃ ψ : AddChar (DHCubic.Residue F p.val) ℂ,
        ψ.IsPrimitive ∧ ∀ t : 𝓞 F,
          ψ (Ideal.Quotient.mk p.val.asIdeal t) =
            R.probe.coefficients.additiveCharacter
              ((t : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) := by
    let I := ThetaBranch.primeIdeal R.A p
    obtain ⟨r, hr, he⟩ := R.probe.allowed.generates I
    let e := ArithGaussCRT.exteriorQuotientEquiv R.A I
    let χ := R.A.residueTraceCharacter R.traceBad I r hr
    let φ := χ.compAddMonoidHom e.toAddMonoidHom
    refine ⟨Circle.coeHom.compAddChar φ,
      (SArithmeticData.traceCharacter_isPrimitive_of_equiv e φ χ (R.A.residueTraceCharacter_squarefree_primitive
        R.traceBad R.probe.allowed.B I p.val.prime.squarefree r hr
        (R.probe.allowed.generator I) he (R.probe.allowed.allowed I)) (fun x => rfl)).compMulHom_of_isPrimitive Subtype.val_injective, ?_⟩
    intro t
    change (R.A.residueTraceCharacter R.traceBad I r hr
      (ArithGaussCRT.exteriorQuotientEquiv R.A I (Ideal.Quotient.mk I.val t)) : ℂ) = _
    rw [ArithGaussCRT.exteriorQuotientEquiv_mk R.A I t,
      R.A.residueTraceCharacter_apply, additiveCharacter_eq_fieldTrace R]
    congr 2
    rw [he]
    rfl
  choose ψ hprim htrace using hp
  exact ⟨ψ, hprim, htrace⟩

end DedekindZetaZeroFree.PrincipalMellinSource

end
