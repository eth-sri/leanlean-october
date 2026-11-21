module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ComplexProjectiveLogNorm
public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteNormTranslationRange

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField

namespace DedekindZetaZeroFree.KPContFlatLogNormSmooth

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteComponent (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPGlobalTorusFunctionData.G F ζ hζ :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

private theorem finiteSubgroup_le_finitePart :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ ≤
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨y, ?_, hyx⟩
  rw [Subgroup.mem_iInf]
  intro w
  rw [MonoidHom.mem_ker, RestrictedProduct.evalMonoidHom_apply]
  exact hy w

theorem finiteComponent_mem (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    finiteComponent F ζ hζ g ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  apply finiteSubgroup_le_finitePart
  have hker : finiteComponent F ζ hζ g ∈ (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [MonoidHom.mem_ker]
    unfold finiteComponent
    rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    simp
  exact RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ hker

end DedekindZetaZeroFree.KPContFlatLogNormSmooth

end

section

noncomputable section
open scoped NumberField Classical BigOperators Matrix Matrix.Norms.Elementwise NNReal
open NumberField

namespace DedekindZetaZeroFree.KPContFlatLogNormSmooth

export HeightGeometry (complexMatrixLogNorm complexMatrixLogNorm_argument_pos
  complexMatrixLogNorm_scalar complexMatrixLogNorm_eq_of_mk_eq complexProjectiveLogNorm
  complexProjectiveLogNorm_mk complexMatrixLogNorm_contDiffOn)

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export KPLiteralChamber (sectionTuple sectionTuple_insertion)

open KPLiteralChamber (leftMatrix leftMatrix_val)

def finiteLogNorm (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℝ :=
  KPContFlatFullProductIwasawa.alpha F ζ hζ (finiteComponent F ζ hζ g)

 lemma compact_insertion (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
  PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w))) ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := by
  rw [show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ from rfl,
   (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  apply list_prod_mem
  intro k hk
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ w (u w)
private lemma finite_component_raw (g : KPGlobalTorusFunctionData.G F ζ hζ) :
  finiteComponent F ζ hζ g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (finiteComponent F ζ hζ g) = 1
  unfold finiteComponent
  rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp

theorem alpha_eq_arch_sum_add_finite
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPContFlatFullProductIwasawa.alpha F ζ hζ g =
      (∑ w : InfinitePlace F, complexProjectiveLogNorm
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w)) +
      finiteLogNorm F ζ hζ g := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ := HeightGeometry.archimedean_factorization F ζ hζ a
  let k := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)))
  have hk : k ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := compact_insertion F ζ hζ u
  have hc : Commute k (finiteComponent F ζ hζ g) :=
   RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _ ⟨_, finite_component_raw F ζ hζ g⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) * k := by
   calc g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * finiteComponent F ζ hζ g := by
         dsimp [a, finiteComponent]; group
        _ = _ := by rw [hfac]; dsimp [k] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  have hn := KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (y w : ℂ))) x (finiteComponent F ζ hζ g)
  change KPContFlatFullProductIwasawa.alpha F ζ hζ ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) = _ at hn
  rw [show KPContFlatFullProductIwasawa.alpha F ζ hζ g = _ from (congrArg (KPContFlatFullProductIwasawa.alpha F ζ hζ) hg).trans (KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ _ ⟨k, hk⟩), hn]
  congr 1
  have hdelta := KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ (fun w => (y w : ℂ)) (fun w => (y w).ne_zero)
  rw [hdelta]
  rw [Real.log_prod (fun w _ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (y w).ne_zero))]
  apply Finset.sum_congr rfl
  intro w _
  unfold complexProjectiveLogNorm complexMatrixLogNorm
  rw [hy w]

theorem finiteComponent_groupArchChart_mul
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (hz : z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
    finiteComponent F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      finiteComponent F ζ hζ g := by
  have hmult : ∀ (u v : PGLComplex.AdelicSlicesRaw.ArchGroup F),
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (u * v) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ u *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ v :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  have hχ : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) :=
    KPLiteralChamber.left_insertion F ζ hζ z
  have hprojχ : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z) =
      fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w)) := by
    rw [hχ, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  unfold finiteComponent
  rw [map_mul (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ), hprojχ, hχ,
    hmult (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w)))
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g)]
  group

theorem alpha_groupArchChart_mul_matrix_formula
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (S : Set (KPGlobalTorusBorelTwistCompatibility.GroupArch F))
    (hS : S ⊆ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)
    (A : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hA : ∀ z ∈ S, ∀ w : InfinitePlace F,
      Matrix.ProjGenLinGroup.mk (A w z) =
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w) :
    ∀ z ∈ S,
      KPContFlatFullProductIwasawa.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      (∑ w : InfinitePlace F,
        Real.log ((‖(A w z : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖A w z 1 0‖ ^ 2 + ‖A w z 1 1‖ ^ 2)) ^ 2)) +
        finiteLogNorm F ζ hζ g := by
  intro z hz
  rw [alpha_eq_arch_sum_add_finite F ζ hζ]
  have h1 : (∑ w : InfinitePlace F, complexProjectiveLogNorm
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w)) =
      ∑ w : InfinitePlace F,
        Real.log ((‖(A w z : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖A w z 1 0‖ ^ 2 + ‖A w z 1 1‖ ^ 2)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro w _
    rw [← hA z hz w]
    exact complexProjectiveLogNorm_mk (A w z)
  have h2 : finiteLogNorm F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      finiteLogNorm F ζ hζ g := by
    unfold finiteLogNorm
    rw [finiteComponent_groupArchChart_mul F ζ hζ g z (hS hz)]
  rw [h1, h2]

theorem alpha_continuous :
    Continuous (KPContFlatFullProductIwasawa.alpha F ζ hζ) := by
  have h := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
    F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ)
  exact h.log (fun g => NNReal.coe_ne_zero.mpr (Units.ne_zero _))

set_option maxHeartbeats 800000 in

theorem alpha_groupArchChart_mul_contDiffOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ ⊤
      (fun z => KPContFlatFullProductIwasawa.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let R : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun w => (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w).out
  let A : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix.GeneralLinearGroup (Fin 2) ℂ := fun w z => leftMatrix (z w) * R w
  let B : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix (Fin 2) (Fin 2) ℂ := fun w z =>
    !![z w 1, z w 1 * z w 2; z w 0 * z w 1, 1 + z w 0 * z w 1 * z w 2] *
      (R w : Matrix (Fin 2) (Fin 2) ℂ)
  have hBA : ∀ w z, z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F →
      B w z = (A w z : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro w z hz
    dsimp [B, A]
    rw [leftMatrix_val _ (hz w)]
  have hA : ∀ z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F,
      ∀ w : InfinitePlace F, Matrix.ProjGenLinGroup.mk (A w z) =
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w := by
    intro z hz w
    have hχ : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) :=
      KPLiteralChamber.left_insertion F ζ hζ z
    rw [hχ, map_mul (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ),
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    dsimp [A, R]
    rw [map_mul]
    congr 1
    exact Quotient.out_eq _
  have hB : ∀ w, ContDiff ℝ ⊤ (B w) := by
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> fun_prop
  have hlocal : ∀ w, ContDiffOn ℝ ⊤ (fun z => complexMatrixLogNorm (B w z))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    intro w
    apply complexMatrixLogNorm_contDiffOn.comp (hB w).contDiffOn
    intro z hz
    rw [Set.mem_setOf_eq, hBA w z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero (A w z)
  have hsum : ContDiffOn ℝ ⊤ (fun z =>
      (∑ w : InfinitePlace F, complexMatrixLogNorm (B w z)) + finiteLogNorm F ζ hζ g)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
    (ContDiffOn.sum (fun w _ => hlocal w)).add contDiffOn_const
  apply hsum.congr
  intro z hz
  have h := alpha_groupArchChart_mul_matrix_formula F ζ hζ g
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) (fun _ h => h) A hA z hz
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [hBA w z hz]
  rfl

end DedekindZetaZeroFree.KPContFlatLogNormSmooth

end
end
