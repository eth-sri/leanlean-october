module

public import DedekindZetaZeroFree.Eisenstein.Sections.CanonicalFlatFamily
public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

section ArchCharacter
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 section

variable (z : KPGlobalTorusFunctionData.TorusArch F)

def archUnit (w : InfinitePlace F) : w.Completionˣ :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
  if h : z w = 0 then 1 else Units.mk0 (e.symm (z w))
    (fun h0 => h (by simpa using congrArg e h0))
 def archIdele : KPGlobalTorusFunctionData.Ideles F where
  val := (fun w => (archUnit F ζ hζ z w).val, 1)
  inv := (fun w => (archUnit F ζ hζ z w).inv, 1)
  val_inv := by
    apply Prod.ext
    · funext w; exact (archUnit F ζ hζ z w).val_inv
    · exact one_mul _
  inv_val := by
    apply Prod.ext
    · funext w; exact (archUnit F ζ hζ z w).inv_val
    · exact one_mul _
private theorem arch_eval (v : KPHilbert.Place F) :
    KPGlobalCubicIdelePairing.ideleEval F v (archIdele F ζ hζ z) =
      (match v with | Sum.inl w => archUnit F ζ hζ z w | Sum.inr q => 1) := by
  cases v with
  | inl w => apply Units.ext; rfl
  | inr q => apply Units.ext; rfl
private theorem arch_cube :
    archIdele F ζ hζ z ∈ CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) := by apply @DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality.ArchimedeanChartCharacter.arch_cube <;> assumption
private theorem arch_tuple :
    KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ (archIdele F ζ hζ z) =
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ z := by apply @DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality.ArchimedeanChartCharacter.arch_tuple <;> assumption

end
 alias arch_center := DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality.arch_center

theorem source_arch_chart_character (z : KPGlobalTorusFunctionData.TorusArch F) :
    ∃ h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H,
      h.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h =
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ h.val) := by
  obtain ⟨c, hc, hχ⟩ := arch_center F ζ hζ z
  have hr : c.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
    Subgroup.mem_sup_right c.property
  let r : KPGlobalCenterRationalCharacter.R F ζ hζ := ⟨c.val, hr⟩
  have hP :=
    KPContFlatSourceRecipe.sourcePolarization_zero F ζ hζ
  refine ⟨⟨c.val, ?_⟩, hc, ?_⟩
  · rw [hP]
    exact hr
  · have he : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character
        ⟨c.val, by rw [hP]; exact hr⟩ = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r := by
      change KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r *
        KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ 0 c.val = _
      have hzero : KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ 0 c.val = 1 := by
        apply Units.ext
        change Complex.exp (0 * _) = 1
        simp
      rw [hzero, mul_one]
    rw [he, KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ r 1 c (by simp [r]), hχ]

end ArchCharacter

theorem source_arch_borel_covariance
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (z : KPGlobalTorusFunctionData.TorusArch F)
    (hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F)
    (x : KPGlobalTorusFunctionData.Adeles F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    t.val.val (((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      ((∏ w : InfinitePlace F, ‖z w‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) * t.val.val g := by
  obtain ⟨h, he, hχ⟩ := source_arch_chart_character F ζ hζ z
  have hc := t.val.property h x g
  rw [he] at hc
  rw [hc, hχ]
  have hd : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero
      (KPGlobalTorusFunctionData.delta F ζ hζ h.val)))
  have hν : (KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ h.val) : ℂ) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ) ^ (1 / 6 : ℝ) : ℝ) := by
    change (((KPGlobalCenterRationalCharacter.nu F ζ hζ h.val : ℝ≥0) : ℝ) : ℂ) = _
    rw [KPGlobalCenterRationalCharacter.nu_formula]
    rfl
  rw [he] at hd hν
  rw [he, hν, KPGlobalTorusFunctionData.deltaHalf, ← Complex.ofReal_mul,
    Real.sqrt_eq_rpow, ← Real.rpow_add hd]
  have hexp : (1 / 2 : ℝ) + 1 / 6 = 2 / 3 := by norm_num
  rw [hexp, KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

end
