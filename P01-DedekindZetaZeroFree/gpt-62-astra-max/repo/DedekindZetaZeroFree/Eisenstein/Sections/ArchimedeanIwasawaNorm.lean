module
public import DedekindZetaZeroFree.Metaplectic.Torus.IwasawaDoubleAveraging

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix
open NumberField
namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by
      intro v; cases v <;> simp [KPAdelicCoverRestrictedProduct.compact])⟩

private alias tuple_prod := DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.tuple_prod

alias ArchimedeanIwasawaNorm.tuple_prod := tuple_prod

private theorem sectionTuple_insertion
    (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (sectionTuple F ζ hζ r)) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (r w)) := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.sectionTuple_insertion <;> assumption

alias ArchimedeanIwasawaNorm.sectionTuple_insertion := sectionTuple_insertion

private lemma gl_map_d {K L : Type*} [Field K] [Field L] (φ : K →+* L) (u v : Kˣ) :
    Matrix.GeneralLinearGroup.map φ (KubotaRankTwo.d K u v) =
      KubotaRankTwo.d L (Units.map φ u) (Units.map φ v) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.map_apply, Units.coe_map]

private lemma gl_map_n {K L : Type*} [Field K] [Field L] (φ : K →+* L) (t : K) :
    Matrix.GeneralLinearGroup.map φ (KubotaRankTwo.n K t) = KubotaRankTwo.n L (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.map_apply]

private lemma archDiagonalTuple_eq_sectionTuple (u : InfinitePlace F → ℂˣ) :
    KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (u w : ℂ)) =
      sectionTuple F ζ hζ (fun w => KubotaRankTwo.d ℂ (u w) 1) := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archDiagonalTuple_eq_sectionTuple <;> assumption

 alias archDiagonalLift_eq_insertion := DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archDiagonalLift_eq_insertion

 section

variable (c : InfinitePlace F → ℂ)

def adeleOfArch : KPGlobalTorusFunctionData.Adeles F :=
  ((fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (c w)), 0)

private theorem rootTuple_eq_sectionTuple :
    KPGlobalTorusFunctionData.rootTuple F ζ hζ (adeleOfArch F ζ hζ c) =
      sectionTuple F ζ hζ (fun w => KubotaRankTwo.n ℂ (c w)) := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.rootTuple_eq_sectionTuple <;> assumption

 theorem N_eq_insertion :
    KPGlobalTorusFunctionData.N F ζ hζ (adeleOfArch F ζ hζ c) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ (c w))) := by
  unfold KPGlobalTorusFunctionData.N
  rw [rootTuple_eq_sectionTuple F ζ hζ c, sectionTuple_insertion]

end

 section

variable (A : Matrix (Fin 2) (Fin 2) ℂ)

def archDen : ℝ := ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2
 def archS : ℝ := Real.sqrt (archDen A)

 lemma archDen_pos (hA : A.det ≠ 0) : 0 < archDen A := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.archDen_pos <;> assumption

private lemma archS_sq : archS A ^ 2 = archDen A :=
  Real.sq_sqrt (by unfold archDen; positivity)

private lemma archS_pos (hA : A.det ≠ 0) : 0 < archS A :=
  Real.sqrt_pos.mpr (archDen_pos A hA)

 def archK : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star (A 1 1) / ((archS A : ℝ) : ℂ), -star (A 1 0) / ((archS A : ℝ) : ℂ);
     A 1 0 / ((archS A : ℝ) : ℂ), A 1 1 / ((archS A : ℝ) : ℂ)]
 def archY (hA : A.det ≠ 0) : ℂˣ :=
  Units.mk0 (A.det / ((archDen A : ℝ) : ℂ))
    (div_ne_zero hA (by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (archDen_pos A hA)))
 def archX : ℂ :=
  (A 0 0 * star (A 1 0) + A 0 1 * star (A 1 1)) / A.det

end

private lemma archK_mem (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    archK A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨Matrix.mem_unitaryGroup_iff.mpr (by
    apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archK_mul_star <;> assumption), (by
    apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archK_det <;> assumption)⟩

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
open scoped Matrix

variable (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0)

private lemma archY_norm :
    ‖(archY A hA : ℂ)‖ = ‖A.det‖ / archDen A := by
  rw [archY, Units.val_mk0, norm_div, Complex.norm_of_nonneg (le_of_lt (archDen_pos A hA))]

private lemma archY_archX_left :
    (archY A hA : ℂ) * (star (A 1 1) + archX A * A 1 0) = A 0 0 := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archY_archX_left <;> assumption

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
open scoped Matrix

private lemma archY_archX_right (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (archY A hA : ℂ) * (-star (A 1 0) + archX A * A 1 1) = A 0 1 := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.archY_archX_right <;> assumption

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
open scoped Matrix

private lemma arch_matrix_identity (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (KubotaRankTwo.d ℂ (archY A hA) 1 : Matrix (Fin 2) (Fin 2) ℂ) *
      (KubotaRankTwo.n ℂ (archX A) : Matrix (Fin 2) (Fin 2) ℂ) * archK A =
      Matrix.scalar (Fin 2) (((archS A : ℝ) : ℂ)⁻¹) * A := by apply @DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.IwasawaDoubleAveraging.arch_matrix_identity <;> assumption

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
open scoped Matrix
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

alias archimedean_factorization := DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization.archimedean_factorization

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

end
