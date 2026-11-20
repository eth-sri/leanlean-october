module

public import DedekindZetaZeroFree.Metaplectic.Torus.ReferenceTensorEvaluation
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FullTorusFormula
open KPGlobalProductPolarizationCharacter KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

private theorem rawProduct_arch_only (x : rawB F ζ hζ P.localData)
    (hf : ∀ q, x.val (Sum.inr q) = 1) :
    rawProduct F ζ hζ P.localData P.adjustment x =
      ∏ w, KPGlobalCenterRationalCharacter.localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w)) := by
  have he (v : KPHilbert.Place F) :
      adjustedLocalValue F ζ hζ P.localData P.adjustment v (rawCoordinate F ζ hζ P.localData x v) =
      (match v with
      | Sum.inl w => KPGlobalCenterRationalCharacter.localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w))
      | Sum.inr _ => 1) := by
    have hv := Classical.choose_spec (raw_coordinate_mem F ζ hζ P.localData x v)
    change (rawCoordinate F ζ hζ P.localData x v).val.val = _ at hv
    cases v with
    | inl w =>
      let := KPGlobalCubicIdelePairing.local_complex_trivial F w
      let z : localCenter F ζ hζ (Sum.inl w) :=
        ⟨(rawCoordinate F ζ hζ P.localData x (Sum.inl w)).val, by exact Subsingleton.elim _ _⟩
      simp only [adjustedLocalValue, P.adjustment.complex_unchanged]
      change (P.localData.localData (Sum.inl w)).lambda _ * 1 = _
      rw [mul_one, (P.localData.localData (Sum.inl w)).extends_center _ z rfl]
      exact localOmega_raw_formula F ζ hζ (Sum.inl w) z _ hv.symm
    | inr q =>
      have hc : rawCoordinate F ζ hζ P.localData x (Sum.inr q) = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hv, hf q, map_one]
        rfl
      rw [hc]
      simp only [adjustedLocalValue, map_one, one_mul]
      convert map_one (P.adjustment.chi (Sum.inr q)) using 1
      congr 1
      apply Subtype.ext
      exact map_one _
  unfold rawProduct
  simp_rw [he]
  let S : Finset (KPHilbert.Place F) := Finset.univ.image Sum.inl
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · exact Finset.prod_image (by intros a ha b hb hab; exact Sum.inl_injective hab)
  · intro v hv
    cases v with
    | inl w => simp [S]
    | inr q => exact False.elim (hv rfl)

theorem lambdaB_arch_only
    (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData)
    (hf : ∀ q, x.val (Sum.inr q) = 1)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x.val) = b.val.val) :
    lambdaB F ζ hζ P.localData P.adjustment b =
      ∏ w, KPGlobalCenterRationalCharacter.localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w)) := (lambdaB_raw_formula F ζ hζ P.localData P.adjustment b x hx).trans
    (rawProduct_arch_only F ζ hζ P x hf)

private theorem norm_phase (ε : rootsOfUnity 3 F) :
    ‖(KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ε : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
  have h : ε ^ 3 = 1 := Subtype.ext ε.property
  have hc : KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ε ^ 3 = 1 := by
    rw [← map_pow, h, map_one]
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hc

private theorem productUnit_arch_only
    (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData)
    (hf : ∀ q, x.val (Sum.inr q) = 1)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x.val) = b.val.val) :
    (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ P.localData P.adjustment b : ℂ) =
      ∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x.val (Sum.inl w)).epsilon : ℂ) := by
  let h w := (KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio F ζ hζ x.val b.val hx (Sum.inl w)).choose
  let p w : (ℝ≥0)ˣ := KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
    (KPGlobalCenterRationalCharacter.localAbs F (Sum.inl w) ((h w).1.unit * (h w).2.unit⁻¹))
    (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inl w) _)))
  have hv w : KPGlobalCenterRationalCharacter.localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w)) =
      KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x.val (Sum.inl w)).epsilon *
        KPGlobalCenterRationalCharacter.positiveComplex (p w) := by
    rw [KPGlobalCenterRationalCharacter.localValue, dite_eq_left (h w)]
    rfl
  have hl := lambdaB_arch_only F ζ hζ P b x hf hx
  simp_rw [hv] at hl
  rw [Finset.prod_mul_distrib] at hl
  rw [← map_prod KPGlobalCenterRationalCharacter.positiveComplex] at hl
  let φ := ∏ w, KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x.val (Sum.inl w)).epsilon
  let pAll := ∏ w, p w
  have hnφ : ‖(φ : ℂ)‖ = 1 := by
    rw [show (φ : ℂ) = ∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x.val (Sum.inl w)).epsilon : ℂ) from
      map_prod (Units.coeHom ℂ) _ _]
    rw [norm_prod]
    simp_rw [norm_phase]
    simp
  have hp (u : (ℝ≥0)ˣ) : ‖(KPGlobalCenterRationalCharacter.positiveComplex u : ℂ)‖ = (u : ℝ) := by
    change ‖((u : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn := lambdaB_norm F ζ hζ P.localData P.adjustment b
  rw [hl, Units.val_mul, norm_mul, hnφ, one_mul, hp] at hn
  have heq : pAll = KPGlobalCenterRationalCharacter.nu F ζ hζ b.val := by
    apply Units.ext
    exact NNReal.eq hn
  change ((lambdaB F ζ hζ P.localData P.adjustment b /
    KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val) : ℂˣ) : ℂ) = _
  rw [hl, ← heq]
  rw [mul_div_cancel_right]
  exact map_prod (Units.coeHom ℂ) _ _

alias raw_diagonal := DedekindZetaZeroFree.KPGlobalTorusTensorFibers.FiniteTensorFunctionalsAndSmoothLevels.raw_diagonal

alias raw_image_torus := DedekindZetaZeroFree.KPGlobalTorusTensorFibers.FiniteTensorFunctionalsAndSmoothLevels.raw_image_torus

private theorem arch_mem_product (raw : RestrictedCover F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = e.val)
    (hf : ∀ q, raw (Sum.inr q) = 1) : e ∈ B F ζ hζ P.localData := by
  intro v
  cases v with
  | inl w => rw [P.localData.complex_full]; trivial
  | inr q =>
    change KPGlobalCubicIdelePairing.localClass F (Sum.inr q)
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (KPGlobalTorusFunctionData.p F ζ hζ e)) ∈ _
    obtain ⟨h, hr⟩ := KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio F ζ hζ raw e he (Sum.inr q)
    have hval : KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (KPGlobalTorusFunctionData.p F ζ hζ e) = 1 := by
      apply Units.ext
      rw [← hr, Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec, IsUnit.unit_spec, hf q]
      simp
    rw [hval, map_one]
    exact Subgroup.one_mem _

theorem finiteTensorRealization_full_raw_formula
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q)
    (raw : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = e.val) :
    (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C S hS
      (PiTensorProduct.tprod ℂ f)).val.val e =
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (raw (Sum.inl w)).epsilon : ℂ)) *
      ∏ᶠ q, KPGlobalTorusFiniteStages.localUntwistedEvaluation F ζ hζ P C q
        (if h : q ∈ S then f ⟨q, h⟩ else KPGlobalTorusFiniteStages.localReference F ζ hζ P C q) (t q) := by
  have hd := raw_diagonal F ζ hζ e raw he
  let xi : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl w => raw (Sum.inl w) | Sum.inr _ => 1,
      Filter.Eventually.of_forall (by intro v; cases v <;> simp [compact])⟩
  let xf : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => raw (Sum.inr q),
      raw.property.mono (by intro v hv; cases v with | inl w => trivial | inr q => exact hv)⟩
  have hdi : ∀ v, (xi v).g 1 0 = 0 ∧ (xi v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => exact hd (Sum.inl w)
    | inr q => simp [xi, KPLocalCover.one_g]
  have hdf : ∀ v, (xf v).g 1 0 = 0 ∧ (xf v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => simp [xf, KPLocalCover.one_g]
    | inr q => exact hd (Sum.inr q)
  let ei : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xi), raw_image_torus F ζ hζ xi hdi⟩
  let ef : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xf), raw_image_torus F ζ hζ xf hdf⟩
  have hsplit : e = ei * ef := by
    apply Subtype.ext
    change e.val = scalarQuotient F ζ hζ (amalgamation F ζ hζ xi) *
      scalarQuotient F ζ hζ (amalgamation F ζ hζ xf)
    rw [← map_mul, ← map_mul, ← he]
    congr 2
    apply RestrictedProduct.ext
    intro v
    change raw v = xi v * xf v
    cases v <;> simp [xi, xf]
  let b : B F ζ hζ P.localData := ⟨ei, arch_mem_product F ζ hζ P xi ei rfl (fun _ => rfl)⟩
  let u := KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C S hS (PiTensorProduct.tprod ℂ f)
  have hu := u.val.property b ef
  change u.val.val (b.val * ef) =
    (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ P.localData P.adjustment b : ℂ) * u.val.val ef at hu
  rw [hsplit]
  rw [hu, (productUnit_arch_only F ζ hζ P b (⟨xi, by
    exact ⟨ei, b.property, rfl⟩⟩) (fun _ => rfl) rfl)]
  rw [KPGlobalTorusFiniteStages.finiteTensorRealization_formula F ζ hζ P C S hS f xf t ef
    (fun _ => rfl) ht rfl]
  rfl
end DedekindZetaZeroFree.EisensteinReferenceSections.FullTorusFormula

end
