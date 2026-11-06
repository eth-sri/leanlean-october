module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.TraceCharactersAndGaussShifts
public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData
public import DedekindZetaZeroFree.Eisenstein.Induction.ExceptionalTorusSphericalSeed
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaHeightRegularity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 theorem height_borel (R : PrincipalMellin.ActualRecipe S η)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) (x : KPAdeles F) (g : Group R) :
    iwasawaLogHeight R ((t.val * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x) * g) =
      Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 t : NNReal) : ℝ) + iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (by exact_mod_cast Units.ne_zero _) (by exact_mod_cast Units.ne_zero _)

 theorem height_compact (R : PrincipalMellin.ActualRecipe S η)
    (g : Group R) (k : fullProductCompact R) : iwasawaLogHeight R (g * k.val) = iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) g k
  rw [h]

 theorem height_one (R : PrincipalMellin.ActualRecipe S η) : iwasawaLogHeight R 1 = 0 := by
  unfold iwasawaLogHeight
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_compact F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) (1 : fullProductCompact R)
  change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) 1 = 1 at h
  rw [h]; simp





























































theorem induced_ordinary_central_covariance (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (f : Functions R)
    (hf : KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 s f)
    (ε : rootsOfUnity 3 F) (g : Group R) :
    f (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 ε * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε : ℂ) * f g := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F R.A.zeta12 R.A.primitive_zeta12 ε
  let r : KPGlobalCenterRationalCharacter.R F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨z.val, Subgroup.mem_sup_right z.property⟩
  have hd : KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 z.val = 1 := by
    apply Units.val_injective
    apply NNReal.rpow_left_injective (show (1 / 6 : ℝ) ≠ 0 by norm_num)
    change (KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 z.val : NNReal) = (1 : NNReal) ^ (1 / 6 : ℝ)
    rw [KPGlobalCenterRationalCharacter.nu_centralRoot]; simp
  have hc := KPGlobalCenterRationalCharacter.lambdaR_genuine F R.A.zeta12 R.A.primitive_zeta12 ε r rfl
  have h := hf.2 r 0 g
  have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  have hz : z.val.val = KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F R.A.zeta12 R.A.primitive_zeta12 ε
  simpa only [r, hz, hN, mul_one,
    KPGlobalExceptionalParameter.realLogPower, hd, hc, Units.val_one, NNReal.coe_one,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using h




























end DedekindZetaZeroFree.ThetaExpansion

end
