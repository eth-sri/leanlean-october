module

public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport
public import DedekindZetaZeroFree.Eisenstein.Induction.TwistedAveragingAndSmoothLevels

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev IwasawaData := KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ

export KPGlobalTorusBorelNormTwistTransport
  (CompactLevel E G GroupArch Induced InducedFunctions InducedLevel ModelData
    Polarization Product Rational Smooth actual_borel_factorization borelDelta borelElement borelP
    borelP_fiberwise borelQ borelQ_fiberwise borelRatio borelRatioHom borelRatio_mul borelRatio_torus
    borel_root borel_torus compactLevelTopology delta_rational groupArchChart groupArchDomain
    groupArchDomain_open groupArchTuple inducedFinalSeminorms inducedJet inducedJetBound
    inducedJetBound_add_le inducedJetBound_smul inducedLevelTopology inducedStageInclusion
    inducedTopology induced_smooth iwasawaNorm iwasawaNorm_borel_mul iwasawaNorm_compact
    iwasawaNorm_formula iwasawaNorm_right_compact iwasawaUpperMul_zero iwasawaUpperRatio
    iwasawaUpperRatio_mul iwasawaUpperRatio_scalar iwasawaUpperRatio_torus
    iwasawaUpperRatio_torus_root iwasawaUpperUnits jet_image_bdd levelRestriction normCharacter
    normPower normPower_continuous normPower_mul normTwist normTwist_formula
    normTwist_inverse_formula productModel projected_root ratio rationalModel restrictLevel twist
    twistedP twistedQ upperRoot upper_units)


 theorem normCharacter_rational (s : ℂ) (y : Fˣ) :
    normCharacter F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.val_injective
  change normPower F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1
  simp [normPower, delta_rational]

local instance smoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

local instance inducedTop (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

theorem finitePart_normal : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
  unfold KPGlobalTorusFunctionData.finitePart
  apply Subgroup.Normal.map (Subgroup.normal_iInf_normal fun w => inferInstance)
  change Function.Surjective (fun x => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x))
  exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

def scalarSection (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P := by
  refine { toFun := fun f => ⟨fun g => (f.val.val g).val.val 1, ?_⟩
           map_add' := ?_
           map_smul' := ?_ }
  · rename_i f
    intro h x g
    have hf := f.val.property h.val x g
    have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 = _ at he
    change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
      (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P h.val (f.val.val g)).val.val 1 at he
    rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val * (P.character h : ℂ) *
        (f.val.val g).val.val 1
    rw [he]
    have hc := (f.val.val g).val.property h 1
    simp only [mul_one] at hc
    change _ * (f.val.val g).val.val h.val = _
    rw [hc]
    exact (mul_assoc _ _ _).symm
  · intros; rfl
  · intros; rfl

theorem scalarSection_formula (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    (scalarSection F ζ hζ P f).val g = (f.val.val g).val.val 1 := by
  unfold scalarSection
  rfl

 theorem scalar_transitivity (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) (t : E F ζ hζ) :
    (f.val.val g).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (scalarSection F ζ hζ P f).val (t.val * g) := by
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hf := f.val.property t 0 g
  simp only [hN, mul_one] at hf
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
    (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f.val.val g)).val.val 1 at he
  rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
  rw [scalarSection_formula, he]
  change _ = _⁻¹ * (_ * _)
  have hp : (0 : ℝ) < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    exact_mod_cast (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)) |> pos_iff_ne_zero.mpr
  have hn : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

local instance compactTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) := compactLevelTopology F ζ hζ P J K

local instance inducedLevelTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    TopologicalSpace (InducedLevel F ζ hζ P J) := inducedLevelTopology F ζ hζ P J

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] smoothTopology inducedFunctionsAddGroup inducedLevelAddGroup
  inducedAddGroup inducedTop compactTop inducedLevelTop

 theorem twistedP_twistedQ (C : ModelData F ζ hζ) (s : ℂ) (f : Rational F ζ hζ s) :
    twistedP F ζ hζ C s (twistedQ F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.periodization_averaging F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

 theorem twistedQ_twistedP (C : ModelData F ζ hζ) (s : ℂ) (f : Product F ζ hζ C s) :
    twistedQ F ζ hζ C s (twistedP F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.averaging_periodization F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

 theorem borelP_borelQ (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelP F ζ hζ C s (borelQ F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelP_fiberwise, borelQ_fiberwise, twistedP_twistedQ]

 theorem borelQ_borelP (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelQ F ζ hζ C s (borelP F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelQ_fiberwise, borelP_fiberwise, twistedQ_twistedP]

private def finiteConj (a : G F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨(MulAut.conjNormal a).toEquiv, ?_, ?_⟩
  · apply Continuous.subtype_mk
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => a * x.val * a⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · apply Continuous.subtype_mk
    have he : (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a).symm = MulAut.conjNormal a⁻¹ := by
      change (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a)⁻¹ = _
      rw [map_inv]
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => ((MulAut.conjNormal a).symm x).val)
    rw [he]
    simp only [MulAut.conjNormal_apply, inv_inv]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private def conjLevel (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  exact ⟨J.toOpenSubgroup.comap (MulAut.conjNormal a⁻¹).toMonoidHom (by
      change Continuous (finiteConj F ζ hζ a⁻¹)
      exact (finiteConj F ζ hζ a⁻¹).continuous),
    (finiteConj F ζ hζ a⁻¹).isCompact_preimage.mpr J.isCompact⟩

 def inducedFunctionsTranslation (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (InducedFunctions F ζ hζ P) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro t x g
        simpa only [mul_assoc] using f.property t x (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

private theorem induced_translate_level (P : Polarization F ζ hζ)
    (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ InducedLevel F ζ hζ P J) :
    inducedFunctionsTranslation F ζ hζ P a f ∈
      InducedLevel F ζ hζ P (conjLevel F ζ hζ a J) := by
  constructor
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val ((groupArchChart F ζ hζ z * g) * a)).val.val 1) _
    simpa only [mul_assoc] using hf.1 (g * a)
  · intro g j
    have hj : a⁻¹ * j.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
      obtain ⟨k, hk, he⟩ := j.property
      have hk' : a⁻¹ * k.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
        letI := finitePart_normal F ζ hζ
        apply Subgroup.mem_map.mpr
        exact ⟨MulAut.conjNormal a⁻¹ k, hk, by simp only [Subgroup.subtype_apply, MulAut.conjNormal_apply, inv_inv]⟩
      change k.val = j.val at he
      rw [← he]
      exact hk'
    have hh := hf.2 (g * a) ⟨a⁻¹ * j.val * a, hj⟩
    change f.val ((g * j.val) * a) = f.val (g * a)
    have he : (g * a) * (a⁻¹ * j.val * a) = (g * j.val) * a := by group
    change f.val ((g * a) * (a⁻¹ * j.val * a)) = f.val (g * a) at hh
    rwa [he] at hh

 theorem induced_translate_union (P : Polarization F ζ hζ) (a : G F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ Induced F ζ hζ P) :
    inducedFunctionsTranslation F ζ hζ P a f ∈ Induced F ζ hζ P := by
  have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ P).comap
      (inducedFunctionsTranslation F ζ hζ P a) := by
    apply iSup_le
    intro J x hx
    exact Submodule.mem_iSup_of_mem (conjLevel F ζ hζ a J)
      (induced_translate_level F ζ hζ P a J x hx)
  exact hle hf

def inducedRightAction (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (Induced F ζ hζ P) where
  toFun a := (inducedFunctionsTranslation F ζ hζ P a).restrict
    (induced_translate_union F ζ hζ P a)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * 1) = f.val.val g
    exact congrArg f.val.val (mul_one g)
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * (a * b)) = f.val.val ((g * a) * b)
    exact congrArg f.val.val (mul_assoc g a b).symm

 theorem inducedRightAction_formula (P : Polarization F ζ hζ)
    (a g : G F ζ hζ) (f : Induced F ζ hζ P) :
    (inducedRightAction F ζ hζ P a f).val.val g = f.val.val (g * a) := by rfl

 theorem borelP_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelP F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a
        (borelP F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  simp only [borelP_fiberwise, inducedRightAction_formula]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

end
