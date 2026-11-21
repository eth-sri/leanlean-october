module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ArchimedeanFactorization

public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import DedekindZetaZeroFree.Eisenstein.Induction.BorelModulusAndIwasawaContinuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ProjectiveWeights.CompactAveraging

@[expose] public section

set_option synthInstance.maxHeartbeats 100000
open scoped Classical BigOperators Matrix.Norms.Elementwise ComplexConjugate
open MeasureTheory Complex

noncomputable section
open scoped NumberField Classical Matrix
open NumberField
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped NumberField Classical Matrix
open NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
export KPLiteralChamber (diagonalUnit leftMatrix complexSectionHom leftMatrix_val)

theorem groupArchChart_eq_archimedeanInsertion
    (x : KPGlobalTorusBorelNormTwistTransport.GroupArch F) :
    KPGlobalTorusBorelNormTwistTransport.groupArchChart F ζ hζ x =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (x w))) :=
  KPLiteralChamber.left_insertion F ζ hζ x

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
noncomputable section
open scoped NumberField Classical NNReal BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
abbrev ArchCompact := InfinitePlace F → KPCplxCharacterHaar.ComplexSU2
 local instance su_compact : CompactSpace KPCplxCharacterHaar.ComplexSU2 := by
  apply isCompact_iff_compactSpace.mp
  exact (show IsCompact (KPCplxCharacterHaar.ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) from by
    convert KPCplxCharacterHaar.complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
 local instance su_group : IsTopologicalGroup KPCplxCharacterHaar.ComplexSU2 where
  continuous_mul := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
  continuous_inv := (continuous_star.comp continuous_subtype_val).subtype_mk _
 local instance archCompactMeas : MeasurableSpace (ArchCompact F) := borel _
 local instance archCompactBorel : BorelSpace (ArchCompact F) := ⟨rfl⟩
 local instance coverGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

def compactInsert (k : ArchCompact F) : G F ζ hζ :=
  PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (k w)))

lemma compactInsert_continuous : Continuous (compactInsert F ζ hζ) := by
  apply (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).1.comp
  apply continuous_pi
  intro w
  apply QuotientGroup.continuous_mk.comp
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.comp (continuous_apply w)
  · rw [show (fun k : ArchCompact F => (KPCplxCharacterHaar.complexSU2Embedding (k w))⁻¹.val) =
      (fun k => (k w)⁻¹.val) by funext k; rw [← map_inv]; rfl]
    exact continuous_subtype_val.comp ((continuous_apply w).inv)

lemma compactInsert_mul (k l : ArchCompact F) :
    compactInsert F ζ hζ (k * l) = compactInsert F ζ hζ k * compactInsert F ζ hζ l := by
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  unfold compactInsert
  change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ =
    RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
  rw [← hih, ← hih, ← hih, ← map_mul]
  congr 1
  funext w
  simp only [Pi.mul_apply, map_mul]

def firstAverage (D : IwasawaData F ζ hζ) (g : G F ζ hζ) : ℝ :=
  ∫ k : ArchCompact F,
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) ∂Measure.haar

lemma firstAverage_compactInsert (D : IwasawaData F ζ hζ) (g : G F ζ hζ)
    (k : ArchCompact F) :
    firstAverage F ζ hζ D (g * compactInsert F ζ hζ k) = firstAverage F ζ hζ D g := by
  unfold firstAverage
  have he : (fun l : ArchCompact F =>
    (((iwasawaNorm F ζ hζ D ((g * compactInsert F ζ hζ k) * compactInsert F ζ hζ l) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) =
    (fun l : ArchCompact F =>
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ (k * l)) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) := by
    funext l
    rw [compactInsert_mul, mul_assoc]
  rw [he]
  exact integral_mul_left_eq_self (μ := (Measure.haar : Measure (ArchCompact F))) (fun l : ArchCompact F => (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ l) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) k

lemma firstAverage_borel (D : IwasawaData F ζ hζ) (t : E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    firstAverage F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) *
        firstAverage F ζ hζ D g := by
  unfold firstAverage
  have he : ∀ k : ArchCompact F,
    (((iwasawaNorm F ζ hζ D (((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) =
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) *
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) := by
    intro k
    rw [mul_assoc, iwasawaNorm_borel_mul, Units.val_mul, NNReal.coe_mul]
    simp only [Real.rpow_eq_pow]
    apply Real.mul_rpow
    all_goals positivity
  simp_rw [he]
  rw [integral_const_mul]

lemma firstAverage_pos (D : IwasawaData F ζ hζ) (g : G F ζ hζ)
    (hcont : Continuous (fun g => (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))) :
    0 < firstAverage F ζ hζ D g := by
  let v (k : ArchCompact F) : ℝ :=
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)
  have hp (k : ArchCompact F) : 0 < v k := by
    dsimp only [v]
    simp only [Real.rpow_eq_pow]
    apply Real.rpow_pos_of_pos
    exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero _)
  have hc : Continuous v := by
    dsimp only [v]
    simp only [Real.rpow_eq_pow]
    apply Continuous.rpow_const
    · exact hcont.comp (continuous_const.mul (compactInsert_continuous F ζ hζ))
    · intro k
      left
      exact_mod_cast (Units.ne_zero (iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k)))
  apply (integral_pos_iff_support_of_nonneg
    (μ := (Measure.haar : Measure (ArchCompact F))) (fun k => (hp k).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have he : Function.support v = Set.univ := by
    ext k
    simp [Function.mem_support, ne_of_gt (hp k)]
  rw [he]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

lemma firstAverage_continuous (D : IwasawaData F ζ hζ)
    (hcont : Continuous (fun g => (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))) :
    Continuous (firstAverage F ζ hζ D) := by
  letI : SecondCountableTopology (G F ζ hζ) := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : LocallyCompactSpace (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  unfold firstAverage
  simp only [Real.rpow_eq_pow]
  have hc : Continuous (fun p : G F ζ hζ × ArchCompact F =>
      (((iwasawaNorm F ζ hζ D (p.1 * compactInsert F ζ hζ p.2) : ℝ≥0) : ℝ)) ^ (-(1:ℝ)/2)) := by
    apply Continuous.rpow_const
    · exact hcont.comp (continuous_fst.mul ((compactInsert_continuous F ζ hζ).comp continuous_snd))
    · intro p
      left
      exact_mod_cast (Units.ne_zero (iwasawaNorm F ζ hζ D (p.1 * compactInsert F ζ hζ p.2)))
  simpa using continuous_parametric_integral_of_continuous
    (μ := (Measure.haar : Measure (ArchCompact F))) hc isCompact_univ

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
open scoped NumberField Classical NNReal BigOperators ComplexConjugate
open NumberField MeasureTheory
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
open ArchRowFactorization ProjectiveAverage
open HeightGeometry (archimedean_factorization)
 local instance coverGroup' : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

def finiteComponent (g : G F ζ hζ) : G F ζ hζ :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

lemma finiteComponent_raw (g : G F ζ hζ) :
    finiteComponent F ζ hζ g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (finiteComponent F ζ hζ g) = 1
  unfold finiteComponent
  rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp

lemma finiteComponent_continuous : Continuous (finiteComponent F ζ hζ) := by
  unfold finiteComponent
  have hc := RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ
  exact ((hc.1.comp hc.2).inv).mul continuous_id

lemma firstAverage_factorization (D : IwasawaData F ζ hζ) (g : G F ζ hζ) :
    firstAverage F ζ hζ D g =
      (∏ w : InfinitePlace F, projectiveRowWeight (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w)) *
        firstAverage F ζ hζ D (finiteComponent F ζ hζ g) := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ := archimedean_factorization F ζ hζ a
  let k := compactInsert F ζ hζ u
  have hc : Commute k (finiteComponent F ζ hζ g) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _
      ⟨_, finiteComponent_raw F ζ hζ g⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
      KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) * k := by
    calc g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * finiteComponent F ζ hζ g := by
              dsimp [a, finiteComponent]; group
         _ = _ := by rw [hfac]; dsimp [k, compactInsert] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  conv_lhs => rw [hg, firstAverage_compactInsert]
  have hb := firstAverage_borel F ζ hζ D
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (y w : ℂ))) x (finiteComponent F ζ hζ g)
  change firstAverage F ζ hζ D ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
    KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) = _ at hb
  rw [hb]
  congr 1
  rw [AnalyticInputs.delta_chart_formula F ζ hζ _ (fun w => (y w).ne_zero)]
  simp only [Real.rpow_eq_pow]
  rw [← Real.finsetProd_rpow _ _ (fun w _ => sq_nonneg ‖(y w : ℂ)‖)]
  apply Finset.prod_congr rfl
  intro w _
  have hn : (‖(y w : ℂ)‖ ^ 2 : ℝ) ^ (-(1:ℝ)/2) = ‖(y w : ℂ)‖⁻¹ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hn, hy w]
  have he : projectiveRowWeight (a w) =
      (‖(a w).out 1 0‖ ^ 2 + ‖(a w).out 1 1‖ ^ 2) / ‖((a w).out.val).det‖ := by
    have hh := projectiveRowWeight_mk (a w).out
    rw [show Matrix.ProjGenLinGroup.mk (a w).out = a w from Quotient.out_eq _] at hh
    exact hh
  rw [he, inv_div]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
open scoped NumberField Classical NNReal BigOperators ComplexConjugate
open NumberField MeasureTheory
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
open ArchRowFactorization ProjectiveAverage
open HeightGeometry (archimedean_factorization)
 local instance coverGroup'' : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

lemma finiteComponent_groupChart (g : G F ζ hζ) (z : GroupArch F) :
    finiteComponent F ζ hζ (groupArchChart F ζ hζ z * g) = finiteComponent F ζ hζ g := by
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  have hmult (u v : PGLComplex.AdelicSlicesRaw.ArchGroup F) :
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (u * v) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ u *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ v := by
    change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ =
      RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
    rw [← hih, ← hih, ← hih]
    exact map_mul ih u v
  have hχ := groupArchChart_eq_archimedeanInsertion F ζ hζ z
  have hp : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (groupArchChart F ζ hζ z) =
      (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) := by
    rw [hχ, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  unfold finiteComponent
  rw [map_mul, hp, hχ, hmult]
  group

 local instance compactD (D : IwasawaData F ζ hζ) : CompactSpace D.K :=
  isCompact_iff_compactSpace.mp D.compact
 local instance measurableD (D : IwasawaData F ζ hζ) : MeasurableSpace D.K := borel _
 local instance borelD (D : IwasawaData F ζ hζ) : BorelSpace D.K := ⟨rfl⟩

lemma secondAverage_smooth (D : IwasawaData F ζ hζ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∫ k : D.K, firstAverage F ζ hζ D ((groupArchChart F ζ hζ z * g) * k.val) ∂Measure.haar)
      (groupArchDomain F) := by
  have hn := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous F ζ hζ D
  let B (k : D.K) (w : InfinitePlace F) :=
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (g * k.val) w
  let h (k : D.K) := firstAverage F ζ hζ D (finiteComponent F ζ hζ (g * k.val))
  let A (z : GroupArch F) (w : InfinitePlace F) := leftMatrix (z w)
  have hB (w : InfinitePlace F) : Continuous (fun k : D.K => B k w) :=
    (continuous_apply w).comp
      ((RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2.comp
        (continuous_const.mul continuous_subtype_val))
  have hh : Continuous h :=
    (firstAverage_continuous F ζ hζ D hn).comp
      ((finiteComponent_continuous F ζ hζ).comp (continuous_const.mul continuous_subtype_val))
  have hA (w : InfinitePlace F) (p q : Fin 2) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : GroupArch F => A z w p q) (groupArchDomain F) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : GroupArch F =>
      (!![z w 1, z w 1 * z w 2; z w 0 * z w 1, 1 + z w 0 * z w 1 * z w 2]) p q) := by
      fin_cases p <;> fin_cases q <;> simp <;> fun_prop
    apply hs.contDiffOn.congr
    intro z hz
    dsimp [A]
    rw [leftMatrix_val _ (hz w)]
    rfl
  have hs := projective_compact_average_smooth (Measure.haar : Measure D.K) B h hB hh
    (groupArchDomain F) A hA
  apply hs.congr
  intro z hz
  apply integral_congr_ae
  filter_upwards [] with k
  rw [firstAverage_factorization, mul_assoc, finiteComponent_groupChart]
  rw [mul_comm (h k)]
  apply congrArg (fun r : ℝ => r * h k)
  apply Finset.prod_congr rfl
  intro w _
  rw [groupArchChart_eq_archimedeanInsertion, map_mul,
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  rfl

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport renaming iwasawa_compactAverage_normalization → iwasawa_compactAverage_normalization
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport renaming iwasawaNorm_pos → iwasawaNorm_pos

lemma genuine_weight_smooth (D : IwasawaData F ζ hζ) (s : ℂ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => iwasawaWeight F ζ hζ D s (groupArchChart F ζ hζ z * g))
      (groupArchDomain F) := by
  have hn := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous F ζ hζ D
  have ha := iwasawa_compactAverage_normalization F ζ hζ D (-(1:ℝ)/2)
    (firstAverage F ζ hζ D) (firstAverage_continuous F ζ hζ D hn)
    (firstAverage_pos F ζ hζ D · hn) (firstAverage_borel F ζ hζ D)
  have hl := GramCoefficients.normalized_average_log_smooth (groupArchDomain F)
    (fun z => (((iwasawaNorm F ζ hζ D (groupArchChart F ζ hζ z * g) : ℝ≥0) : ℝ)))
    (fun z => ∫ k : D.K, firstAverage F ζ hζ D ((groupArchChart F ζ hζ z * g) * k.val) ∂Measure.haar)
    (∫ k : D.K, firstAverage F ζ hζ D k.val ∂Measure.haar)
    ha.1 (fun z _ => iwasawaNorm_pos F ζ hζ D _) (secondAverage_smooth F ζ hζ D g)
    (fun z _ => ha.2 _)
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hl)).cexp

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

end
end
end
