module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility
public import DedekindZetaZeroFree.Eisenstein.Induction.BorelModulusAndIwasawaContinuity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration
public import DedekindZetaZeroFree.Eisenstein.Induction.ExceptionalParameterExponents
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarRealization.Continuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarRealization.FiniteLevelContinuity

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairing

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev E := KPGlobalTorusFunctionData.E F ζ hζ

abbrev Iwasawa := KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ
abbrev Level := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ

def sourcePolarization (s : ℂ) :=
  KPGlobalTorusBorelTwistCompatibility.twist F ζ hζ
    (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) s

def targetExponentPolarization (s : ℂ) :=
  KPGlobalTorusBorelTwistCompatibility.twist F ζ hζ
    (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) (-1 / 3 - s)

theorem projW :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) =
    QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (KPAdelicCoverRestrictedProduct.rationalBase F (KPStandardLocalRootLifts.weylSwap F)) := by
  change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
    (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _) = _
  unfold KPCubicCoverConstruction.adelicW
  rw [KPRationalAdelicSplitting.W_rational]
  rfl
 theorem wSq :
    (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) *
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) = 1 := by
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _ *
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _ = _
  rw [← map_mul]
  have hw : KPRationalAdelicSplitting.W F ζ hζ * KPRationalAdelicSplitting.W F ζ hζ = 1 :=
    by simpa [pow_two] using KPRationalAdelicSplitting.W_sq F ζ hζ
  rw [hw, map_one]
theorem adelicW_inv_eq_self_rationalPeriodizationPairingData :
    (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ =
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) :=
  inv_eq_of_mul_eq_one_left (wSq F ζ hζ)
 theorem conjugation_mem (t : E F ζ hζ) :
    (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ ∈ E F ζ hζ := by
  obtain ⟨A, ha, h10, h01⟩ := t.property
  let W := KPAdelicCoverRestrictedProduct.rationalBase F (KPStandardLocalRootLifts.weylSwap F)
  refine ⟨W * A * W, ?_, ?_, ?_⟩
  · simp only [map_mul, adelicW_inv_eq_self_rationalPeriodizationPairingData, projW]
    rw [ha]
  · simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap,
      Matrix.mul_apply, Fin.sum_univ_two, h01]
  · simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap,
      Matrix.mul_apply, Fin.sum_univ_two, h10]

def weylTorusConjugation : E F ζ hζ ≃* E F ζ hζ where
  toFun t := ⟨(KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹, conjugation_mem F ζ hζ t⟩
  invFun t := ⟨(KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹, conjugation_mem F ζ hζ t⟩
  left_inv t := by
    apply Subtype.ext
    change (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) *
        ((KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
        (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹) *
        (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ = t.val
    rw [adelicW_inv_eq_self_rationalPeriodizationPairingData]
    simp only [← mul_assoc, wSq, one_mul]
    rw [mul_assoc, wSq, mul_one]
  right_inv t := by
    apply Subtype.ext
    change (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) *
        ((KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
        (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹) *
        (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ = t.val
    rw [adelicW_inv_eq_self_rationalPeriodizationPairingData]
    simp only [← mul_assoc, wSq, one_mul]
    rw [mul_assoc, wSq, mul_one]
  map_mul' t u := by
    simp

theorem weylTorusConjugation_formula (t : E F ζ hζ) :
    (weylTorusConjugation F ζ hζ t).val =
      KPCubicCoverConstruction.adelicW F ζ hζ * t.val *
        (KPCubicCoverConstruction.adelicW F ζ hζ)⁻¹ := by rfl

def weylPolarization (s : ℂ) : KPGlobalTorusFunctionData.Polarization F ζ hζ where
  H := (sourcePolarization F ζ hζ s).H.comap (weylTorusConjugation F ζ hζ).toMonoidHom
  closed := by
    apply (sourcePolarization F ζ hζ s).closed.preimage
    apply Continuous.subtype_mk
    fun_prop
  abelian := by
    intro h k
    apply Subtype.ext
    apply (weylTorusConjugation F ζ hζ).injective
    change weylTorusConjugation F ζ hζ (h.val * k.val) =
      weylTorusConjugation F ζ hζ (k.val * h.val)
    simp only [map_mul]
    exact congrArg Subtype.val ((sourcePolarization F ζ hζ s).abelian
      ⟨weylTorusConjugation F ζ hζ h.val, h.property⟩
      ⟨weylTorusConjugation F ζ hζ k.val, k.property⟩)
  contains_center := by
    intro z hz
    apply (sourcePolarization F ζ hζ s).contains_center
    change weylTorusConjugation F ζ hζ z ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨u, rfl⟩ := (weylTorusConjugation F ζ hζ).surjective t
    exact (map_mul _ _ _).symm.trans ((congrArg (weylTorusConjugation F ζ hζ)
      ((Subgroup.mem_center_iff.mp hz) u)).trans (map_mul _ _ _))
  character := (sourcePolarization F ζ hζ s).character.comp
    ⟨((weylTorusConjugation F ζ hζ).toMonoidHom.comp
      ((sourcePolarization F ζ hζ s).H.comap
        (weylTorusConjugation F ζ hζ).toMonoidHom).subtype).codRestrict
        (sourcePolarization F ζ hζ s).H (fun t => t.property), by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          change Continuous (fun t : (sourcePolarization F ζ hζ s).H.comap
            (weylTorusConjugation F ζ hζ).toMonoidHom =>
              (weylTorusConjugation F ζ hζ t.val).val)
          fun_prop⟩

namespace ActualWeylFibreProof
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming diagonalPGL_torusRatio → diagonalPGL_torusRatio
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming diagonalPGL_injective → diagonalPGL_injective
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming restrictedProjection_eq_diagonal → restrictedProjection_eq_diagonal
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming normPower_mul → normPower_mul
variable {F ζ hζ}
set_option backward.isDefEq.respectTransparency false
theorem diagonalLift_eq_rationalPglA_rationalPeriodizationPairingData (y : KPGlobalTorusFunctionData.Ideles F) :
    KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ y =
      KPRationalAdelicSplitting.pglA F ζ hζ y := by rfl
theorem torusRatio_diagonalLift_rationalPeriodizationPairingData (y : KPGlobalTorusFunctionData.Ideles F) (t : E F ζ hζ)
    (ht : t.val = KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ y) :
    KPGlobalTorusFunctionData.p F ζ hζ t = y := by
  obtain ⟨t', ht', hp'⟩ := KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.standard_diagonal_torus_ratio
    F ζ hζ y (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y) (fun _ => rfl)
  have htt : t = t' := Subtype.ext (ht.trans ht'.symm)
  exact htt ▸ hp'
private theorem proj_diagonal (y : KPGlobalTorusFunctionData.Ideles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ y) =
        KPGlobalCubicIdelePairing.diagonalPGL F y := by
  change QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y)) = _
  rw [restrictedProjection_eq_diagonal F ζ hζ y
    (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y) (fun _ => rfl)]
  rfl
theorem torusRatio_weylConjugation_inv_rationalPeriodizationPairingData (t : E F ζ hζ) :
    KPGlobalTorusFunctionData.p F ζ hζ (weylTorusConjugation F ζ hζ t) =
      (KPGlobalTorusFunctionData.p F ζ hζ t)⁻¹ := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let W := KPAdelicCoverRestrictedProduct.rationalBase F (KPStandardLocalRootLifts.weylSwap F)
  have hW : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (weylTorusConjugation F ζ hζ t).val =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (W * A * W) := by
    rw [weylTorusConjugation_formula]
    change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      ((KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) * t.val *
        (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹) = _
    rw [adelicW_inv_eq_self_rationalPeriodizationPairingData]
    simp only [map_mul, projW]
    rw [hA]
  have h10' : (W * A * W) 1 0 = 0 := by
    simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two, h01]
  have h01' : (W * A * W) 0 1 = 0 := by
    simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two, h10]
  have h1 := KPGlobalTorusFunctionData.ratio_formula F
    ⟨_, (weylTorusConjugation F ζ hζ t).property⟩ (W * A * W) hW.symm h10' h01'
  have h0 := KPGlobalTorusFunctionData.ratio_formula F ⟨_, t.property⟩ A hA h10 h01
  have he0 : (KPGlobalTorusFunctionData.diagonal_entries_units F (W * A * W) h10' h01').1.unit =
      (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec]
    simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap,
      Matrix.mul_apply, Fin.sum_univ_two]
  have he1 : (KPGlobalTorusFunctionData.diagonal_entries_units F (W * A * W) h10' h01').2.unit =
      (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec]
    simp [W, KPAdelicCoverRestrictedProduct.rationalBase, KPStandardLocalRootLifts.weylSwap,
      Matrix.mul_apply, Fin.sum_univ_two]
  change (((KPGlobalTorusFunctionData.p F ζ hζ (weylTorusConjugation F ζ hζ t)) : KPGlobalTorusFunctionData.Adeles F)) = (KPGlobalTorusFunctionData.diagonal_entries_units F (W * A * W) h10' h01').1.unit.val * (KPGlobalTorusFunctionData.diagonal_entries_units F (W * A * W) h10' h01').2.unit⁻¹.val at h1
  apply Units.ext
  rw [h1, he0, he1]
  have hu : KPGlobalTorusFunctionData.p F ζ hζ t =
      (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit *
      (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit⁻¹ := Units.ext h0
  rw [hu]
  rfl
theorem weylConjugation_diagonalLift_inv_rationalPeriodizationPairingData (y : KPGlobalTorusFunctionData.Ideles F)
    (t : E F ζ hζ) (ht : t.val = KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ y) :
    (weylTorusConjugation F ζ hζ t).val =
      KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ y⁻¹ := by
  rw [weylTorusConjugation_formula]
  change (KPRationalAdelicSplitting.pglW F ζ hζ * t.val) *
    (KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ = _
  rw [ht, diagonalLift_eq_rationalPglA_rationalPeriodizationPairingData, KPRationalAdelicSplitting.quotient_weyl_diagonal]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rfl
private theorem weyl_root (ε : rootsOfUnity 3 F) :
    weylTorusConjugation F ζ hζ (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val =
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val := by
  apply Subtype.ext
  rw [weylTorusConjugation_formula, KPGlobalCenterRationalCharacter.centralRoot_formula]
  have hc := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    (show KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩)
  rw [(Subgroup.mem_center_iff.mp hc _), mul_assoc]
  simp
private theorem center_decomp (z : KPGlobalTorusFunctionData.Z F ζ hζ) :
    ∃ (ε : rootsOfUnity 3 F) (y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F)),
      z = KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε *
        KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y := by
  have hp : KPGlobalTorusFunctionData.p F ζ hζ z.val ∈
      CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) := by
    rw [← Subgroup.mem_comap,
      ← KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.covered_torus_center_eq_cubes]
    exact z.property
  let y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) := ⟨_, hp⟩
  let c := KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y
  have he : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val.val =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ c.val.val := by
    rw [KPGlobalCenterRationalCharacter.cubeLift_formula, proj_diagonal]
    exact (diagonalPGL_torusRatio F
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val.val, z.val.property⟩).symm
  have hk : z.val.val * c.val.val⁻¹ ∈
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    simp_all
  rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel] at hk
  obtain ⟨ε, hε⟩ := hk
  refine ⟨ε, y, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change z.val.val = _ * c.val.val
  rw [KPGlobalCenterRationalCharacter.centralRoot_formula, hε]
  group
theorem weyl_rational (a : Fˣ) :
    weylTorusConjugation F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) =
      KPGlobalTorusFunctionData.s F ζ hζ a⁻¹ := by
  apply Subtype.ext
  rw [weylTorusConjugation_formula]
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPRationalAdelicSplitting.W F ζ hζ) *
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ (KPGlobalTorusFunctionData.rationalDiagonal F a)) *
    (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPRationalAdelicSplitting.W F ζ hζ))⁻¹ = _
  have hs (a : Fˣ) : (KPGlobalTorusFunctionData.s F ζ hζ a).val =
      KPRationalAdelicSplitting.pglA F ζ hζ
        (Units.map (algebraMap F (KPGlobalTorusFunctionData.Adeles F)).toMonoidHom a) := 
    (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
      (KPRationalAdelicSplitting.A_rational F ζ hζ a)).symm
  change (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) *
    (KPGlobalTorusFunctionData.s F ζ hζ a).val *
    (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ = _
  rw [hs]
  change KPRationalAdelicSplitting.pglW F ζ hζ * _ *
    (KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ = _
  rw [KPRationalAdelicSplitting.quotient_weyl_diagonal]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [hs, map_inv]
theorem weylConjugation_mem_rationalCenter_iff_rationalPeriodizationPairingData (t : E F ζ hζ) :
    weylTorusConjugation F ζ hζ t ∈ KPGlobalCenterRationalCharacter.R F ζ hζ ↔
      t ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := by
  rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage,
    Subgroup.mem_comap, MonoidHom.comp_apply, torusRatio_weylConjugation_inv_rationalPeriodizationPairingData, map_inv, Subgroup.inv_mem_iff,
    ← MonoidHom.comp_apply, ← Subgroup.mem_comap]
 def weylCenter (z : KPGlobalTorusFunctionData.Z F ζ hζ) :
    KPGlobalTorusFunctionData.Z F ζ hζ :=
  ⟨weylTorusConjugation F ζ hζ z.val, by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨u, rfl⟩ := (weylTorusConjugation F ζ hζ).surjective t
    exact (map_mul _ _ _).symm.trans ((congrArg (weylTorusConjugation F ζ hζ)
      ((Subgroup.mem_center_iff.mp z.property) u)).trans (map_mul _ _ _))⟩
theorem weylCenter_mul (z c : KPGlobalTorusFunctionData.Z F ζ hζ) :
    weylCenter (z * c) = weylCenter z * weylCenter c := Subtype.ext (map_mul _ _ _)
theorem weylCenter_cube (y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F)) :
    weylCenter (KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y) =
      KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (weylConjugation_diagonalLift_inv_rationalPeriodizationPairingData y.val _ (KPGlobalCenterRationalCharacter.cubeLift_formula F ζ hζ y)).trans
    (KPGlobalCenterRationalCharacter.cubeLift_formula F ζ hζ y⁻¹).symm
theorem positiveComplex_sixthPower_eq_normPower_rationalPeriodizationPairingData (t : E F ζ hζ) :
    (KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.sixthPower (KPGlobalTorusFunctionData.delta F ζ hζ t)) : ℂ) =
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (1 / 6) t := by
  have hp : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    simp
  change (((((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = _
  rw [Real.rpow_def_of_pos hp, Complex.ofReal_exp]
  unfold KPGlobalTorusBorelTwistCompatibility.normPower
  congr 1
  push_cast
  ring
theorem normPower_weyl (s : ℂ) (t : E F ζ hζ) :
    KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s (weylTorusConjugation F ζ hζ t) =
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-s) t := by
  unfold KPGlobalTorusBorelTwistCompatibility.normPower KPGlobalTorusFunctionData.delta
  change Complex.exp (s * (Real.log (((KPGlobalTorusFunctionData.ideleAbs F
    (KPGlobalTorusFunctionData.p F ζ hζ (weylTorusConjugation F ζ hζ t)) : ℝ≥0) : ℝ)) : ℂ)) = _
  rw [torusRatio_weylConjugation_inv_rationalPeriodizationPairingData, map_inv]
  simp only [Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, Complex.ofReal_neg]
  simp
private theorem omega_weyl (z : KPGlobalTorusFunctionData.Z F ζ hζ) :
    (KPGlobalCenterRationalCharacter.omegaA F ζ hζ (weylCenter z) : ℂ) =
      (KPGlobalCenterRationalCharacter.omegaA F ζ hζ z : ℂ) *
        KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-1 / 3) z.val := by
  obtain ⟨ε, y, rfl⟩ := center_decomp z
  rw [weylCenter_mul]
  have hr : weylCenter (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε) =
      KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε := Subtype.ext (weyl_root ε)
  rw [hr, weylCenter_cube, map_mul, map_mul,
    KPGlobalCenterRationalCharacter.omegaA_cube, KPGlobalCenterRationalCharacter.omegaA_cube]
  simp only [Subgroup.coe_mul]
  rw [normPower_mul]
  have hroot : KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-1 / 3)
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1 := by

    have hp : KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1 := by
      apply diagonalPGL_injective F
      rw [map_one]
      have he := diagonalPGL_torusRatio F
        ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val,
          (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.property⟩
      change KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.p F ζ hζ
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val) =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val at he
      rw [he, KPGlobalCenterRationalCharacter.centralRoot_formula]
      exact MonoidHom.mem_ker.mp (KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ ▸
        (show KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
          (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩))
    simp [KPGlobalTorusBorelTwistCompatibility.normPower, KPGlobalTorusFunctionData.delta, hp]
  have hp (y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F)) :
      (KPGlobalCenterRationalCharacter.positiveComplex
        (KPGlobalCenterRationalCharacter.sixthPower (KPGlobalTorusFunctionData.ideleAbs F y.val)) : ℂ) =
        KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (1 / 6)
          (KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y).val := by
    have he := positiveComplex_sixthPower_eq_normPower_rationalPeriodizationPairingData (KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y).val
    change _ = _ at he
    simpa only [KPGlobalTorusFunctionData.delta, MonoidHom.comp_apply,
      torusRatio_diagonalLift_rationalPeriodizationPairingData y.val _ (KPGlobalCenterRationalCharacter.cubeLift_formula F ζ hζ y)] using he
  simp only [Units.val_mul, hroot, one_mul, hp]
  have hw := normPower_weyl (1 / 6) (KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y).val
  change KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (1 / 6)
    (weylCenter (KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y)).val = _ at hw
  rw [weylCenter_cube] at hw
  rw [hw, mul_assoc]
  congr 1
  unfold KPGlobalTorusBorelTwistCompatibility.normPower
  rw [← Complex.exp_add]
  congr 1
  ring
theorem lambdaR_weylConjugation_inverseCubeNorm_rationalPeriodizationPairingData (t : KPGlobalCenterRationalCharacter.R F ζ hζ) :
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      ⟨weylTorusConjugation F ζ hζ t.val, (weylConjugation_mem_rationalCenter_iff_rationalPeriodizationPairingData t.val).2 t.property⟩ : ℂ) =
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ t : ℂ) *
        KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-1 / 3) t.val := by
  obtain ⟨a, z, hz⟩ := (KPGlobalCenterRationalCharacter.R_eq_product F ζ hζ t.val).mp t.property
  have hw : KPGlobalTorusFunctionData.s F ζ hζ a⁻¹ * (weylCenter z).val =
      weylTorusConjugation F ζ hζ t.val := by
    rw [← hz, map_mul, weyl_rational]
    rfl
  rw [KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ _ a⁻¹ (weylCenter z) hw,
    KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ t a z hz, omega_weyl]
  rw [← hz, normPower_mul]
  have hr : KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-1 / 3)
      (KPGlobalTorusFunctionData.s F ζ hζ a) = 1 := by
    simp [KPGlobalTorusBorelTwistCompatibility.normPower,
      KPGlobalTorusBorelTwistCompatibility.delta_rational]
  rw [hr, one_mul]
end ActualWeylFibreProof

theorem actual_weyl_fibre (s : ℂ) :
    weylPolarization F ζ hζ s = targetExponentPolarization F ζ hζ s := by
  open ActualWeylFibreProof in
    have hh : (weylPolarization F ζ hζ s).H = (targetExponentPolarization F ζ hζ s).H := by
      ext t
      exact weylConjugation_mem_rationalCenter_iff_rationalPeriodizationPairingData t
    have hc : ∀ (t : (weylPolarization F ζ hζ s).H),
        (weylPolarization F ζ hζ s).character t =
        (targetExponentPolarization F ζ hζ s).character ⟨t.val, hh ▸ t.property⟩ := by
      intro t
      have htR : t.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := (weylConjugation_mem_rationalCenter_iff_rationalPeriodizationPairingData t.val).1 t.property
      apply Units.ext
      change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
        ⟨weylTorusConjugation F ζ hζ t.val, t.property⟩ : ℂ) *
        KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s
          (weylTorusConjugation F ζ hζ t.val) =
        (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
          ⟨t.val, htR⟩ : ℂ) *
          KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ (-1 / 3 - s) t.val
      rw [lambdaR_weylConjugation_inverseCubeNorm_rationalPeriodizationPairingData ⟨t.val, htR⟩, normPower_weyl, mul_assoc]
      congr 1
      unfold KPGlobalTorusBorelTwistCompatibility.normPower
      rw [← Complex.exp_add]
      congr 1
      ring
    generalize hp : weylPolarization F ζ hζ s = P at hh hc ⊢
    generalize hq : targetExponentPolarization F ζ hζ s = Q at hh hc ⊢
    cases P with
    | mk H closed abelian contains character =>
      cases Q with
      | mk H' closed' abelian' contains' character' =>
        dsimp only at hh
        cases hh
        have he : character = character' := by
          ext t
          exact congrArg Units.val (hc t)
        cases he
        rfl

abbrev targetPolarization (s : ℂ) := weylPolarization F ζ hζ s

abbrev Source (s : ℂ) := KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
  (sourcePolarization F ζ hζ s)

abbrev NormOne (D : Iwasawa F ζ hζ) :=
  {g : G F ζ hζ // KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g = 1}

def angularRelation (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (g g' : NormOne F ζ hζ D) : Prop :=
  ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val * u.val

def angularSetoid (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (angularRelation F ζ hζ D U)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩

abbrev Omega (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :=
  Quotient (angularSetoid F ζ hζ D U)

instance (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    MeasurableSpace (Omega F ζ hζ D U) := borel _

def fullAngularSetoid (D : Iwasawa F ζ hζ) : Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (fun g g' => ∃ (y : Fˣ)
    (x : KPGlobalTorusFunctionData.Adeles F),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩

abbrev FullOmega (D : Iwasawa F ζ hζ) := Quotient (fullAngularSetoid F ζ hζ D)

instance (D : Iwasawa F ζ hζ) : MeasurableSpace (FullOmega F ζ hζ D) := borel _

end DedekindZetaZeroFree.KPMsRationalCompactCrossPairing

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairing

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ

 theorem wInv :
    (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ)⁻¹ =
      (KPCubicCoverConstruction.adelicW F ζ hζ : G F ζ hζ) :=
  inv_eq_of_mul_eq_one_left (wSq F ζ hζ)

namespace ActualWeylFibreProof
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming diagonalPGL_torusRatio → diagonalPGL_torusRatio
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming diagonalPGL_injective → diagonalPGL_injective
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct renaming restrictedProjection_eq_diagonal → restrictedProjection_eq_diagonal
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming normPower_mul → normPower_mul
variable {F ζ hζ}
set_option backward.isDefEq.respectTransparency false

 theorem p_weyl (t : E F ζ hζ) :
    KPGlobalTorusFunctionData.p F ζ hζ (weylTorusConjugation F ζ hζ t) =
      (KPGlobalTorusFunctionData.p F ζ hζ t)⁻¹ := by apply DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.ActualWeylFibreProof.torusRatio_weylConjugation_inv_rationalPeriodizationPairingData <;> assumption

end ActualWeylFibreProof

abbrev Target (s : ℂ) := KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
  (targetPolarization F ζ hζ s)

def scalarSmooth (P : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Submodule ℂ (KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P) :=
  (KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ P).range

def sourceCore (D : Iwasawa F ζ hζ) : Submodule ℂ (Source F ζ hζ 0) :=
  KPGlobalEisensteinData.hcHeckeCore
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (sourcePolarization F ζ hζ 0)).comp D.K.subtype)
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (sourcePolarization F ζ hζ 0)).comp
        (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
    (scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0))

def targetCore (D : Iwasawa F ζ hζ) : Submodule ℂ (Target F ζ hζ 0) :=
  KPGlobalEisensteinData.hcHeckeCore
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (targetPolarization F ζ hζ 0)).comp D.K.subtype)
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (targetPolarization F ζ hζ 0)).comp
        (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
    (scalarSmooth F ζ hζ (targetPolarization F ζ hζ 0))

abbrev Vplus (D : Iwasawa F ζ hζ) := sourceCore F ζ hζ D
abbrev Vminus (D : Iwasawa F ζ hζ) := targetCore F ζ hζ D

def fixedPlus (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    Submodule ℂ (Vplus F ζ hζ D) where
  carrier := {f | ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    f.val.val (g * u.val) = f.val.val g}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x u; simp [hf x u, hg x u]
  smul_mem' := by simp_all

def fixedMinus (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    Submodule ℂ (Vminus F ζ hζ D) where
  carrier := {v | ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    v.val.val (g * u.val) = v.val.val g}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x u; simp [hf x u, hg x u]
  smul_mem' := by simp_all

def fullToLevel (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    FullOmega F ζ hζ D → Omega F ζ hζ D U := by
  refine Quotient.lift (fun g => Quotient.mk (angularSetoid F ζ hζ D U) g) ?_
  intro a b hab
  apply Quotient.sound
  have hrel : ∀ a b, (fullAngularSetoid F ζ hζ D).r a b →
      (angularSetoid F ζ hζ D U).r a b := by
    apply Relation.EqvGen.mono
    rintro g g' ⟨y, x, h⟩
    exact ⟨y, x, 1, by simpa using h⟩
  exact hrel a b hab

def angularForget (D : Iwasawa F ζ hζ) (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) :
    Omega F ζ hζ D V → Omega F ζ hζ D U := by
  apply Quotient.map id
  apply Relation.EqvGen.mono
  rintro g g' ⟨y, x, u, hu⟩
  have hm : KPGlobalTorusFunctionData.globalLevel F ζ hζ V ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono h
  exact ⟨y, x, ⟨u.val, hm u.property⟩, hu⟩

def sourceStage (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (T : KPGlobalEisensteinData.CompactTypeStage
      ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
        (sourcePolarization F ζ hζ 0)).comp D.K.subtype)) :=
  KPGlobalEisensteinData.finiteLevelTypeStage _
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (sourcePolarization F ζ hζ 0)).comp
        (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
    (scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0)) U T

structure RawCompactComparison (C : ModelData F ζ hζ) (D : Iwasawa F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where

  atlasLevel : Level F ζ hζ → KPMsFixedHaarDisintegration.Level F ζ hζ
  level_matching : ∀ U,
    KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
      (atlasLevel U).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype
  fullBeta : Measure (FullOmega F ζ hζ D)
  fullBeta_finite : IsFiniteMeasure fullBeta
  fullBeta_positive : 0 < fullBeta Set.univ
  fullBeta_open_positive : fullBeta.IsOpenPosMeasure
  fullCompact : CompactSpace (FullOmega F ζ hζ D)
  beta : ∀ U, Measure (Omega F ζ hζ D U)
  beta_from_full : ∀ U, Measure.map (fullToLevel F ζ hζ D U) fullBeta = beta U
  fullSourceAngular : Vplus F ζ hζ D →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ)
  fullTargetAngular : Vminus F ζ hζ D →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ)
  full_source_formula : ∀ f (g : NormOne F ζ hζ D),
    fullSourceAngular f (Quotient.mk _ g) = f.val.val g.val
  full_target_formula : ∀ v (g : NormOne F ζ hζ D),
    fullTargetAngular v (Quotient.mk _ g) = v.val.val g.val
  beta_finite : ∀ U, IsFiniteMeasure (beta U)
  beta_positive : ∀ U, 0 < beta U Set.univ
  beta_open_positive : ∀ U, (beta U).IsOpenPosMeasure
  compact : ∀ U, CompactSpace (Omega F ζ hζ D U)
  shape : ∀ U, Omega F ζ hζ D U →
    KPMsFixedHaarDisintegration.Omega (H.atlas (atlasLevel U))
  shape_measurable : ∀ U, Measurable (shape U)

  shape_measure : ∀ U, Measure.map (shape U) (beta U) =
    (H.disintegration (atlasLevel U)).beta
  beta_compatible : ∀ V U h,
    Measure.map (angularForget F ζ hζ D V U h) (beta V) = beta U

  sourceFlat : ∀ s, Vplus F ζ hζ D →ₗ[ℂ] Source F ζ hζ s
  targetFlat : ∀ s, Vminus F ζ hζ D →ₗ[ℂ] Target F ζ hζ s

  sourceFlat_recipe : ∀ s f g, (sourceFlat s f).val g =
    Complex.exp (s * (Real.log
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) : ℂ)) *
      f.val.val g

  targetFlat_recipe : ∀ s v g, (targetFlat s v).val g =
    Complex.exp (-s * (Real.log
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) : ℂ)) *
      v.val.val g
  sourceFlat_zero : ∀ f, sourceFlat 0 f = f.val
  targetFlat_zero : ∀ v, targetFlat 0 v = v.val
  sourceFlat_compact : ∀ s f k, (sourceFlat s f).val (k : D.K) = f.val.val k
  targetFlat_compact : ∀ s v k, (targetFlat s v).val (k : D.K) = v.val.val k
  sourceAngular : ∀ U, fixedPlus F ζ hζ D U →ₗ[ℂ] (Omega F ζ hζ D U → ℂ)
  targetAngular : ∀ U, fixedMinus F ζ hζ D U →ₗ[ℂ] (Omega F ζ hζ D U → ℂ)

  source_formula : ∀ U f (g : NormOne F ζ hζ D),
    sourceAngular U f (Quotient.mk _ g) = f.val.val.val g.val
  target_formula : ∀ U v (g : NormOne F ζ hζ D),
    targetAngular U v (Quotient.mk _ g) = v.val.val.val g.val

section Detection
variable {F ζ hζ}

theorem compact_radialSection_eq_diagonalLift (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) :
    KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r =
      KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ (B.ell r) := by
  unfold KPMsFixedHaarDisintegration.radialSection KPGlobalTorusFunctionData.archDiagonalLift
    KPGlobalCenterRationalCharacter.diagonalLift
  congr 2
  apply Subtype.ext
  funext v
  cases v with
  | inl w =>
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple,
      KPGlobalCenterRationalCharacter.diagonalTuple]
    have hz : KPMsFixedHaarDisintegration.positiveSlots F B.slot r w ≠ 0 := by
      unfold KPMsFixedHaarDisintegration.positiveSlots
      split_ifs
      · exact_mod_cast (Real.sqrt_pos.2 r.property).ne'
      simp
    simp only [dif_neg hz]
    congr 1
    apply Units.ext
    change _ = KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w) (B.ell r : KPAdeles F)
    rw [B.ell_slots]
    rfl
  | inr q =>
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple,
      KPGlobalCenterRationalCharacter.diagonalTuple]
    have he : KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (B.ell r) = 1 := by
      apply Units.ext
      exact B.ell_finite r q
    rw [he]
    simp

theorem compact_radialSection_mem_center (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) :
    ∃ t : KPGlobalTorusFunctionData.Z F ζ hζ,
      t.val.val = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r := by
  let y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) :=
    ⟨B.ell r, B.ell_cube r⟩
  refine ⟨KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y, ?_⟩
  rw [KPGlobalCenterRationalCharacter.cubeLift_formula, compact_radialSection_eq_diagonalLift]

 theorem compact_radialSection_delta (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) :
    (((KPGlobalTorusFunctionData.delta F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ
        (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)) : ℝ≥0) : ℝ)) = r.val := by
  change (((KPGlobalTorusFunctionData.ideleAbs F
    (KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ
        (KPMsFixedHaarDisintegration.positiveSlots F B.slot r))) : ℝ≥0) : ℝ)) = r.val
  rw [B.lift_ratio, B.ell_norm]

theorem compact_radial_lambdaR (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius)
    (t : KPGlobalCenterRationalCharacter.R F ζ hζ)
    (ht : t.val.val = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r) :
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ t : ℂ) =
      KPGlobalExceptionalParameter.realLogPower r.val (1 / 6) := by
  let y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) :=
    ⟨B.ell r, B.ell_cube r⟩
  let z := KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y
  have hz : z.val = t.val := by
    apply Subtype.ext
    rw [KPGlobalCenterRationalCharacter.cubeLift_formula, ht, compact_radialSection_eq_diagonalLift]
  rw [KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ t 1 z (by simpa using hz),
    KPGlobalCenterRationalCharacter.omegaA_cube]
  change ((Real.rpow (((KPGlobalTorusFunctionData.ideleAbs F (B.ell r) : ℝ≥0) : ℝ)) (1 / 6) : ℝ) : ℂ) = _
  rw [B.ell_norm]
  change ((r.val ^ (1 / 6 : ℝ) : ℝ) : ℂ) = _
  rw [Real.rpow_def_of_pos r.property]
  rw [KPGlobalExceptionalParameter.realLogPower, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem compact_source_radial_covariance (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (s : ℂ) (r : KPMsFixedHaarDisintegration.Radius)
    (f : Source F ζ hζ s) (g : G F ζ hζ) :
    f.val (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * g) =
      KPGlobalExceptionalParameter.realLogPower r.val
        (KPGlobalExceptionalParameter.sourceExponent s) * f.val g := by
  obtain ⟨z, hz⟩ := compact_radialSection_mem_center B r
  let t : (sourcePolarization F ζ hζ s).H :=
    ⟨z.val, Subgroup.mem_sup_right z.property⟩
  have ht : t.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (KPMsFixedHaarDisintegration.positiveSlots F B.slot r) := Subtype.ext hz
  have hd : (((KPGlobalTorusFunctionData.delta F ζ hζ t.val : ℝ≥0) : ℝ)) = r.val := by
    rw [ht]
    exact compact_radialSection_delta B r
  have hh : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val =
      KPGlobalExceptionalParameter.realLogPower r.val (1 / 2) := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    rw [hd, Real.sqrt_eq_rpow, Real.rpow_def_of_pos r.property]
    rw [KPGlobalExceptionalParameter.realLogPower, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hc : ((sourcePolarization F ζ hζ s).character t : ℂ) =
      KPGlobalExceptionalParameter.realLogPower r.val (1 / 6) *
        KPGlobalExceptionalParameter.realLogPower r.val s := by
    change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ t : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t.val = _
    rw [compact_radial_lambdaR B r t hz]
    simp only [KPGlobalTorusBorelTwistCompatibility.normPower, hd,
      KPGlobalExceptionalParameter.realLogPower]
  have he := f.property t 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  change f.val ((t.val.val * KPGlobalTorusFunctionData.N F ζ hζ 0) * g) = _ at he
  rw [hn, mul_one, hz, hh, hc, ← mul_assoc,
    KPGlobalExceptionalParameter.source_multiplier r.val r.property s] at he
  exact he

theorem compact_target_radial_covariance (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (s : ℂ) (r : KPMsFixedHaarDisintegration.Radius)
    (f : Target F ζ hζ s) (g : G F ζ hζ) :
    f.val (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * g) =
      KPGlobalExceptionalParameter.realLogPower r.val
        (KPGlobalExceptionalParameter.weylExponent s) * f.val g := by
  have hp : targetPolarization F ζ hζ s = sourcePolarization F ζ hζ (-1 / 3 - s) :=
    actual_weyl_fibre F ζ hζ s
  let f' : Source F ζ hζ (-1 / 3 - s) := ⟨f.val, by
    change f.val ∈ KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
      (sourcePolarization F ζ hζ (-1 / 3 - s))
    rw [← hp]
    exact f.property⟩
  have he := compact_source_radial_covariance B (-1 / 3 - s) r f' g
  have hx : KPGlobalExceptionalParameter.sourceExponent (-1 / 3 - s) =
      KPGlobalExceptionalParameter.weylExponent s := by
    unfold KPGlobalExceptionalParameter.sourceExponent KPGlobalExceptionalParameter.weylExponent
    ring
  simpa only [hx] using he

end Detection

namespace CompactCoreTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
variable {F ζ hζ}

local instance inducedTopology (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    TopologicalSpace (KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ Q) :=
  KPGlobalTorusBorelTwistCompatibility.inducedTopology F ζ hζ Q

 theorem scalarSmooth_exists_right_level (U₀ : Level F ζ hζ)
    (P₀ : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (v : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P₀)
    (hv : v ∈ scalarSmooth F ζ hζ P₀) :
    ∃ U : Level F ζ hζ, ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      v.val (g * u.val) = v.val g := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hv
  let fixed := fun b : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P₀ =>
    ∃ U : Level F ζ hζ, ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      b.val (g * u.val) = b.val g
  have hb : fixed b.val := by
    apply Submodule.iSup_induction _ (motive := fixed) b.property
    · intro U b hb
      exact ⟨U, hb.2⟩
    · exact ⟨U₀, fun _ _ => rfl⟩
    · intro b c hb hc
      obtain ⟨U, hU⟩ := hb
      obtain ⟨V, hV⟩ := hc
      let W : Level F ζ hζ :=
        ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
          U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
      have hWU : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono inf_le_left
      have hWV : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ V := Subgroup.map_mono inf_le_right
      refine ⟨W, ?_⟩
      intro g u
      change b.val _ + c.val _ = b.val g + c.val g
      rw [hU g ⟨u.val, hWU u.property⟩, hV g ⟨u.val, hWV u.property⟩]
  obtain ⟨U, hU⟩ := hb
  exact ⟨U, fun g u => by
    simp only [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hU g u]⟩

end CompactCoreTransport

section Pairing
variable {F ζ hζ}
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : RawCompactComparison F ζ hζ C D R P H)

 theorem compact_core_scalar_continuous
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (hf : f ∈ scalarSmooth F ζ hζ Q) : Continuous f.val := by
  obtain ⟨p, hp⟩ := hf
  rw [← hp]
  exact KPMsResidualTailRestoration.OutgoingTailL2.AngularBound.scalarSection_continuous_of_levels Q
    (KPMsResidualTailRestoration.OutgoingTailL2.AngularBound.inducedLevel_scalar_continuous Q) p

 theorem compact_source_core_smooth :
    sourceCore F ζ hζ D ≤ scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0) := by
  unfold sourceCore KPGlobalEisensteinData.hcHeckeCore
  apply iSup_le
  intro J
  apply iSup_le
  intro T
  exact le_trans inf_le_left inf_le_left

 theorem compact_target_core_smooth :
    targetCore F ζ hζ D ≤ scalarSmooth F ζ hζ (targetPolarization F ζ hζ 0) := by
  unfold targetCore KPGlobalEisensteinData.hcHeckeCore
  apply iSup_le
  intro J
  apply iSup_le
  intro T
  exact le_trans inf_le_left inf_le_left

section ArbitraryUProof
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace ArbitraryCorePairing
open KPMsRationalCompactCrossPairing

open KPMsRationalCompactCrossPairing.CompactCoreTransport
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : RawCompactComparison F ζ hζ C D R P H)

end ArbitraryCorePairing

end ArbitraryUProof

theorem radial_angular_decomposition (U : Level F ζ hζ)
    (s : ℂ) (r : KPMsFixedHaarDisintegration.Radius)
    (f : fixedPlus F ζ hζ D U) (v : fixedMinus F ζ hζ D U)
    (g : NormOne F ζ hζ D) :
    (A.sourceFlat s f.val).val
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot r * g.val) =
      KPGlobalExceptionalParameter.realLogPower r.val
        (KPGlobalExceptionalParameter.sourceExponent s) *
          A.sourceAngular U f (Quotient.mk _ g) ∧
    (A.targetFlat s v.val).val
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot r * g.val) =
      KPGlobalExceptionalParameter.realLogPower r.val
        (KPGlobalExceptionalParameter.weylExponent s) *
          A.targetAngular U v (Quotient.mk _ g) := by
  have hp : (A.sourceFlat s f.val).val g.val = f.val.val.val g.val := by
    rw [A.sourceFlat_recipe]
    simp [g.property]
  have hm : (A.targetFlat s v.val).val g.val = v.val.val.val g.val := by
    rw [A.targetFlat_recipe]
    simp [g.property]
  exact ⟨(compact_source_radial_covariance
      (H.disintegration (A.atlasLevel U)).radial s r (A.sourceFlat s f.val) g.val).trans
        (by rw [hp, A.source_formula]),
    (compact_target_radial_covariance
      (H.disintegration (A.atlasLevel U)).radial s r (A.targetFlat s v.val) g.val).trans
        (by rw [hm, A.target_formula])⟩

 theorem actual_full_source_continuous (f : Vplus F ζ hζ D) :
    Continuous (A.fullSourceAngular f) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  simpa only [Function.comp_def, Quotient.mk', A.full_source_formula] using
    (compact_core_scalar_continuous _ _ (compact_source_core_smooth f.property)).comp
      continuous_subtype_val

theorem full_radial_angular_decomposition
    (U : Level F ζ hζ) (s : ℂ) (r : KPMsFixedHaarDisintegration.Radius)
    (f : Vplus F ζ hζ D) (v : Vminus F ζ hζ D) (g : NormOne F ζ hζ D) :
    (A.sourceFlat s f).val
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot r * g.val) =
      KPGlobalExceptionalParameter.realLogPower r.val (2 / 3 + s) *
        A.fullSourceAngular f (Quotient.mk _ g) ∧
    (A.targetFlat s v).val
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot r * g.val) =
      KPGlobalExceptionalParameter.realLogPower r.val (1 / 3 - s) *
        A.fullTargetAngular v (Quotient.mk _ g) := by
  obtain ⟨J, hJ⟩ := CompactCoreTransport.scalarSmooth_exists_right_level U _ f.val
    (compact_source_core_smooth f.property)
  obtain ⟨L, hL⟩ := CompactCoreTransport.scalarSmooth_exists_right_level U _ v.val
    (compact_target_core_smooth v.property)
  let fJ : fixedPlus F ζ hζ D J := ⟨f, hJ⟩
  let vL : fixedMinus F ζ hζ D L := ⟨v, hL⟩
  have hpf := (radial_angular_decomposition A J s ⟨1, by norm_num⟩ fJ 0 g).1
  have hmv := (radial_angular_decomposition A L s ⟨1, by norm_num⟩ 0 vL g).2
  have hf : (A.sourceFlat s f).val g.val = f.val.val g.val := by
    simpa only [(H.disintegration (A.atlasLevel J)).radial.section_one,
      one_mul, KPGlobalExceptionalParameter.realLogPower, Real.log_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, A.source_formula] using hpf
  have hv : (A.targetFlat s v).val g.val = v.val.val g.val := by
    simpa only [(H.disintegration (A.atlasLevel L)).radial.section_one,
      one_mul, KPGlobalExceptionalParameter.realLogPower, Real.log_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, A.target_formula] using hmv
  rw [A.full_source_formula, A.full_target_formula]
  constructor
  · rw [compact_source_radial_covariance, hf]
    rfl
  · rw [compact_target_radial_covariance, hv]
    rfl
