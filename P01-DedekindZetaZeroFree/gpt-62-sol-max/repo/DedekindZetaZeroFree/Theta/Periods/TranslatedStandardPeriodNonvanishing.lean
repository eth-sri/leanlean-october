module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import DedekindZetaZeroFree.Adeles.Characters.RationalFrequencyNontriviality
public import DedekindZetaZeroFree.Eisenstein.Residues.GenericityAndPeriodNonvanishing

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped NumberField Pointwise Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod
open KPGlobalResidualConstruction

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actual_upper_root_continuous : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) :=
  KPGlobalTorusFunctionData.continuous_N F ζ hζ

private theorem globalRoot_eq_pglN (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := by
  rfl

 theorem globalRoot_rationalDiagonal_conjugation (t : Fˣ)
    (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x *
        KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
        KPGlobalTorusFunctionData.N F ζ hζ
          (algebraMap F (KPGlobalTorusFunctionData.Adeles F) (↑t⁻¹ : F) * x) := by
  let y : KPGlobalTorusFunctionData.Ideles F := Units.map
    (algebraMap F (KPGlobalTorusFunctionData.Adeles F)).toMonoidHom t
  have hy : KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPRationalAdelicSplitting.pglA F ζ hζ y := by
    unfold KPRationalAdelicSplitting.pglA
    dsimp [y]
    rw [KPRationalAdelicSplitting.A_rational]
    rfl
  simp_rw [hy, globalRoot_eq_pglN]
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ x y
  convert h using 2
  congr 1
  rw [mul_comm]
  rfl

private theorem B_one_left (v : KPHilbert.Place F) (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 a
private theorem B_one_right (v : KPHilbert.Place F) (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 a
 theorem local_weyl_upper_swap (v : KPHilbert.Place F) (x : KPHilbert.Completion F v) :
    KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.N F ζ hζ v x =
    KPStandardLocalRootLifts.LowerN F ζ hζ v x * KPStandardLocalRootLifts.W F ζ hζ v := by
  unfold KPStandardLocalRootLifts.W KPStandardLocalRootLifts.N KPStandardLocalRootLifts.LowerN
  change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
  congr 1
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, KPStandardLocalRootLifts.lowerN,
        KubotaRankTwo.n, Matrix.mul_apply, KPLocalCover.sectionMap]
  · simp only [KPLocalCover.sectionMap_g, KPLocalCover.sectionMap_epsilon, one_mul]
    have hX : KubotaRankTwo.X (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.lowerN (KPHilbert.Completion F v) x *
          KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F v)) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.lowerN,
        KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]
    have hW : KubotaRankTwo.X (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F v)) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
    have hd : KubotaRankTwo.det (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.lowerN (KPHilbert.Completion F v) x) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.det, KPStandardLocalRootLifts.lowerN, Matrix.det_fin_two]
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      hX, hW, hd, B_one_left, B_one_right]
theorem adelic_weyl_upper_swap (x : KPAdelicCoverRestrictedProduct.Adeles F) :
    KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x =
    KPRationalAdelicSplitting.pglLowerN F ζ hζ x * KPRationalAdelicSplitting.pglW F ζ hζ := by
  have hh : KPRationalAdelicSplitting.W F ζ hζ * KPRationalAdelicSplitting.N F ζ hζ x =
      KPRationalAdelicSplitting.LowerN F ζ hζ x * KPRationalAdelicSplitting.W F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ *
        KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ =
      KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ *
        KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _
    rw [← map_mul, ← map_mul]
    congr 1
    apply RestrictedProduct.ext
    intro v
    exact local_weyl_upper_swap F ζ hζ v _
  have hN : KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := by
    unfold KPGlobalTorusFunctionData.N KPRationalAdelicSplitting.pglN KPRationalAdelicSplitting.N
    congr 2
  rw [hN]
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ) hh

theorem adelic_lower_eq_weyl_upper (x : KPAdelicCoverRestrictedProduct.Adeles F) :
    KPRationalAdelicSplitting.pglLowerN F ζ hζ x =
      KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ := by
  rw [adelic_weyl_upper_swap, mul_inv_cancel_right]

theorem lower_invariance_of_upper (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ x g, θ (KPGlobalTorusFunctionData.N F ζ hζ x * g) = θ g)
    (hw : ∀ g, θ (KPRationalAdelicSplitting.pglW F ζ hζ * g) = θ g) :
    ∀ x g, θ (KPRationalAdelicSplitting.pglLowerN F ζ hζ x * g) = θ g := by
  have hwi : ∀ g, θ ((KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ * g) = θ g := by
    intro g
    simpa using (hw ((KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ * g)).symm
  intro x g
  rw [adelic_lower_eq_weyl_upper, mul_assoc, mul_assoc, hw, hu, hwi]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem actual_rational_diagonal_conjugation (t : Fˣ) (x : A F) :
    KPGlobalTorusFunctionData.N F ζ hζ x * KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
        KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F (A F) (↑t⁻¹ : F) * x) := by
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ x
    (Units.map (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)).toMonoidHom t)
  unfold KPRationalAdelicSplitting.pglA at h
  have he : KPRationalAdelicSplitting.A F ζ hζ
      (Units.map (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)).toMonoidHom t) =
        KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KubotaRankTwo.d F t 1) := by
    exact KPRationalAdelicSplitting.A_rational F ζ hζ t
  rw [he] at h
  change KPGlobalTorusFunctionData.N F ζ hζ x * KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
    KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
      KPGlobalTorusFunctionData.N F ζ hζ (x * (algebraMap F (A F) (↑t⁻¹ : F))) at h
  simpa only [mul_comm x] using h

end DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod

end
end
