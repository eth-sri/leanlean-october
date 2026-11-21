module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPFiniteCuspAtlas

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteParameter (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPGlobalTorusFunctionData.Adeles F := (0,z)

theorem finite_root_mem
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z) ∈
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  unfold KPGlobalTorusFunctionData.N KPAdelicCoverRestrictedProduct.scalarQuotient
    KPCuspGenuineMonodromy.archProjection
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.lift_mk']
  simp only [MonoidHom.comp_apply, KPAdelicCoverRestrictedProduct.projection_amalgamation]
  funext w
  change Matrix.ProjGenLinGroup.mk
    (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
      (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
        (KPGlobalTorusFunctionData.rootTuple F ζ hζ (finiteParameter F z)))) = 1
  change Matrix.ProjGenLinGroup.mk
    (KPLocalCover.projection F ζ hζ (Sum.inl w)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w)
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w) (finiteParameter F z)))) = 1
  simp [finiteParameter, KPAdelicCoverRestrictedProduct.adeleEval,
    KPStandardLocalRootLifts.N, KPLocalCover.sectionMap, KPLocalCover.projection,
    KubotaRankTwo.n, RingHom.fst]
  have he : Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))
      (by simp [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  change Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) _ ∈ _
  exact he.symm ▸ Subgroup.one_mem _

def finiteRoot
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  ⟨KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z), finite_root_mem F ζ hζ z⟩

end DedekindZetaZeroFree.KPFiniteCuspAtlas
