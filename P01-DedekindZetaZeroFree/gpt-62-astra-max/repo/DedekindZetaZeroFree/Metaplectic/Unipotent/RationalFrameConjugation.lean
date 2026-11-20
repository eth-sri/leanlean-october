module

public import DedekindZetaZeroFree.Geometry.PGL.Horospheres.RationalRootAction
public import DedekindZetaZeroFree.Adeles.Approximation.UpperRoots.FiniteRootReduction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

alias archProjection_compare := DedekindZetaZeroFree.KPMsFixedHaar.archProjection_compare

alias insertion_commutes_cover := DedekindZetaZeroFree.KPMsActualCuspSource.insertion_commutes

def complexParameter (a : NumberField.InfiniteAdeleRing F) : NumberField.InfinitePlace F → ℂ :=
  fun w => NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w) (a w)

private theorem map_upper {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    Matrix.GeneralLinearGroup.map f (KubotaRankTwo.n K t) = KubotaRankTwo.n L (f t) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.coe_n]

theorem root_arch_insertion (a : NumberField.InfiniteAdeleRing F) :
    KPGlobalTorusFunctionData.N F ζ hζ (a,0) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRoot (complexParameter F ζ hζ a)) := by
  unfold archRoot
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  simp only [map_upper]
  simp only [complexParameter, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  let l := (Finset.univ : Finset (NumberField.InfinitePlace F)).toList
  let f := fun w => localToRestricted F ζ hζ (Sum.inl w)
    (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (a w))
  have ht : KPGlobalTorusFunctionData.rootTuple F ζ hζ (a,0) = (l.map f).prod := by
    apply Subtype.ext
    funext v
    let p : RestrictedCover F ζ hζ →* KPLocalCover.CubicGL2Raw F ζ hζ v :=
      RestrictedProduct.evalMonoidHom (KPLocalCover.CubicGL2Raw F ζ hζ)
        (B := compact F ζ hζ) v
    change _ = p ((l.map f).prod)
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def]
    cases v with
    | inl w =>
      rw [List.prod_map_eq_pow_single w (fun v => p (f v)) (by
        intro v hv _
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply, hv])]
      rw [(List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp [l])), pow_one]
      simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
        KPGlobalTorusFunctionData.rootTuple, adeleEval, RingHom.fst]
      rfl
    | inr q =>
      have hf : ∀ w, p (f w) = 1 := by
        intro w
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply]
      simp [hf, KPGlobalTorusFunctionData.rootTuple, adeleEval, RingHom.snd, KPStandardLocalRootLifts.N_zero]
      exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ (KPGlobalTorusFunctionData.rootTuple F ζ hζ (a,0))) = _
  rw [ht, map_list_prod, map_list_prod]
  simp only [List.map_map]
  rfl

private alias projective_equiv_injective := DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.projective_equiv_injective

alias complex_kernel_mem := DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.complex_kernel_mem

theorem rationalLift_archProjection (σ : KPCuspArithmetic.PGL2 F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ) = archRational σ := by apply @DedekindZetaZeroFree.KPMsActualCuspSource.rationalLift_archProjection <;> assumption

theorem rationalLift_split (σ : KPCuspArithmetic.PGL2 F) :
    ∃ s : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      KPMsClearedTruncationL2.rationalLift F ζ hζ σ =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val := by
  let r := KPMsClearedTruncationL2.rationalLift F ζ hζ σ
  let i := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ)
  have hm : i⁻¹ * r ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    apply complex_kernel_mem
    rw [map_mul, map_inv]
    change (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (archRational σ)))⁻¹ *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ r = 1
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, rationalLift_archProjection,
      inv_mul_cancel]
  exact ⟨⟨i⁻¹ * r, hm⟩, by change r = i * (i⁻¹ * r); group⟩

private theorem conjugation_split {G : Type} [Group G] (i s z n : G)
    (hsz : Commute s z) (his : Commute i s) (hin : Commute i n) :
    (i * s) * (z * n) * (i * s)⁻¹ =
      (i * z * i⁻¹) * (s * n * s⁻¹) := by
  rw [mul_inv_rev, hsz.mul_mul_mul_comm]
  calc
    _ =
        (i * z) * (s * n) * (i⁻¹ * s⁻¹) := by rw [his.symm.inv_left.inv_right.eq]
    _ = (i * z) * i⁻¹ * ((s * n) * s⁻¹) := (((his.symm.mul_left hin.symm).inv_right).mul_mul_mul_comm (i * z) s⁻¹).trans (by group)
    _ = _ := by group

theorem conjugated_root_split (σ : KPCuspArithmetic.PGL2 F)
    (s : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hs : KPMsClearedTruncationL2.rationalLift F ζ hζ σ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val)
    (a : NumberField.InfiniteAdeleRing F)
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPMsClearedTruncationL2.rationalLift F ζ hζ σ *
      KPGlobalTorusFunctionData.N F ζ hζ (a,z) *
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ)⁻¹ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (archRational σ * archRoot (complexParameter F ζ hζ a) * (archRational σ)⁻¹) *
      (s * finiteRoot F ζ hζ z * s⁻¹).val := by
  have he : (a,z) = (a, (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) + (0,z) := by
    apply Prod.ext <;> simp
  rw [he, KPGlobalTorusFunctionData.N_add, root_arch_insertion, hs]
  change (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val) *
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRoot (complexParameter F ζ hζ a)) *
      (finiteRoot F ζ hζ z).val) *
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val)⁻¹ =
    _ * (s.val * (finiteRoot F ζ hζ z).val * s.val⁻¹)
  rw [conjugation_split _ _ _ _
    (insertion_commutes_cover F ζ hζ _ s).symm
    (insertion_commutes_cover F ζ hζ _ s)
    (insertion_commutes_cover F ζ hζ _ (finiteRoot F ζ hζ z))]
  congr 1
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  change _ = RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
  rw [← hih, map_mul, map_mul, map_inv]
  simp only [hih]
  rfl

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
