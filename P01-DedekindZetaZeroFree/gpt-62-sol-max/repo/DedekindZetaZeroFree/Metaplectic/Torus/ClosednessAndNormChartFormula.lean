module

public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

open scoped NumberField Classical Matrix NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.AnalyticInputs
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct KPGlobalTorusFunctionData
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
private theorem archmatrix (z : TorusArch F) :
    let A := restrictedProjection F ζ hζ (archDiagonalTuple F ζ hζ z)
    A 1 0 = 0 ∧ A 0 1 = 0 ∧ A 1 1 = 1 := by
  dsimp [restrictedProjection, matrixValue, matrixEntry]
  constructor
  · apply Prod.ext
    · funext w
      change _ = 0
      simp [archDiagonalTuple, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
    · apply RestrictedProduct.ext
      intro w
      change _ = 0
      simp [archDiagonalTuple]
  constructor
  · apply Prod.ext
    · funext w
      change _ = 0
      simp [archDiagonalTuple, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
    · apply RestrictedProduct.ext
      intro w
      change _ = 0
      simp [archDiagonalTuple]
  · apply Prod.ext
    · funext w
      change _ = 1
      simp [archDiagonalTuple, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
    · apply RestrictedProduct.ext
      intro w
      change _ = 1
      simp [archDiagonalTuple]
private theorem archp (z : TorusArch F) :
    (p F ζ hζ (torusArchChart F ζ hζ z) : KPAdelicCoverRestrictedProduct.Adeles F) =
      (restrictedProjection F ζ hζ (archDiagonalTuple F ζ hζ z)) 0 0 := by
  let A := restrictedProjection F ζ hζ (archDiagonalTuple F ζ hζ z)
  obtain ⟨h10, h01, h11⟩ := archmatrix F ζ hζ z
  have hq : QuotientGroup.mk' (scalarSubgroup F) A =
      pglProjection F ζ hζ (torusArchChart F ζ hζ z).val := rfl
  have hr := ratio_formula F
    ⟨pglProjection F ζ hζ (torusArchChart F ζ hζ z).val,
      (torusArchChart F ζ hζ z).property⟩ A hq h10 h01
  change (torusRatio F ⟨pglProjection F ζ hζ (torusArchChart F ζ hζ z).val,
      (torusArchChart F ζ hζ z).property⟩ : KPAdelicCoverRestrictedProduct.Adeles F) = _
  rw [hr]
  have h1 : (diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    simpa using h11
  rw [h1]
  simp [A]
private theorem archp_finite (z : TorusArch F) :
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (p F ζ hζ (torusArchChart F ζ hζ z))).2 = 1 := by
  apply (IdeleGroup.finiteEquivFiniteAdeleUnits (K := F)).injective
  apply Units.ext
  have hr := congrArg Prod.snd (archp F ζ hζ z)
  change _ = (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  change _ = (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) at hr
  have he := congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.2)
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply
      (p F ζ hζ (torusArchChart F ζ hζ z)))
  change _ = (p F ζ hζ (torusArchChart F ζ hζ z)).val.2 at he
  change (IdeleGroup.finiteEquivFiniteAdeleUnits (K := F)
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (p F ζ hζ (torusArchChart F ζ hζ z))).2).val = _ at he
  exact he.trans hr
private theorem archp_infinite (z : TorusArch F)
    (hz : z ∈ torusArchDomain F) (w : InfinitePlace F) :
    ((InfiniteIdeleGroup.component w
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
        (p F ζ hζ (torusArchChart F ζ hζ z))).1 : w.Completionˣ) : w.Completion) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (z w) := by
  have hr := congrArg (fun a : KPAdelicCoverRestrictedProduct.Adeles F => a.1 w)
    (archp F ζ hζ z)
  have he := congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.1 w)
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply
      (p F ζ hζ (torusArchChart F ζ hζ z)))
  change ((InfiniteIdeleGroup.component w
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (p F ζ hζ (torusArchChart F ζ hζ z))).1 : w.Completionˣ) : w.Completion) = _ at he
  rw [he, hr]
  simp [restrictedProjection, matrixValue, matrixEntry, archDiagonalTuple,
    KPStandardLocalRootLifts.A, KPLocalCover.sectionMap, hz w]

theorem delta_chart_formula (z : TorusArch F) (hz : z ∈ torusArchDomain F) :
    (((delta F ζ hζ (torusArchChart F ζ hζ z) : ℝ≥0) : ℝ)) =
      ∏ w : InfinitePlace F, ‖z w‖ ^ 2 := by
  change (((IdeleGroup.absoluteNorm
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (p F ζ hζ (torusArchChart F ζ hζ z))))⁻¹ : ℝ≥0ˣ) : ℝ) = _
  rw [IdeleGroup.absoluteNorm_apply, archp_finite F ζ hζ z, map_one, one_mul, inv_inv,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, nnnormUnitHom_val,
    NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  apply Finset.prod_congr rfl
  intro w _
  rw [archp_infinite F ζ hζ z hz w,
    (KPHilbert.infinite_isComplex F ζ hζ w).mult_eq_two]
  congr 1
  let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  have h := e.symm.isometry.dist_eq (z w) 0
  change dist ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (z w))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm 0) = _ at h
  simpa only [dist_zero_right, map_zero] using h

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.AnalyticInputs

section

open scoped NumberField Classical Matrix NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.AnalyticInputs
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct KPGlobalTorusFunctionData
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem actualtorusclosed : IsClosed (torus F ζ hζ : Set (KPGlobalTorusFunctionData.G F ζ hζ)) :=
  KPGlobalTorusFunctionData.torus_closed F ζ hζ
end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.AnalyticInputs

end
