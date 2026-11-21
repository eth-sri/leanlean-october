module

public import DedekindZetaZeroFree.Arithmetic.PGL.Cusps.TranslationLattice
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.FiniteOrbifoldAtlas
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.FiniteInvariantMeasure
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.RadialQuotientDisintegration

@[expose] public section

noncomputable section
open scoped Classical Matrix
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPCuspCharts

export KPCuspChart (Horizontal Shape Cross Coordinates embedding translationLattice Torus Base toArch
  affine crossRelation CrossQuotient highRelation HighQuotient homeomorphAction AffineOrbit
  kernelUnits CoarseFiber coarseProjection totalRelation TotalQuotient crossAffine radialMeasure)

abbrev ParabolicData := KPCuspChart.ExtensionData
abbrev BundleAtlas := KPCuspChart.AtlasData

theorem toArch_meanHeight (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (p : Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (toArch F p) = p.2 := by
  have hb : ∑ i, (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i = 0 := p.1.2.property
  have hn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [KPCuspLogShape.meanHeight, toArch, Finset.sum_add_distrib, hb,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ p.2 hn

structure ChartOutput (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    extends KPCuspChart.GeometryData F hF S D where
  positive_dimension : 0 < KPCuspLogShape.dimension F
  lattice : ∃ hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule,
    letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule
  actual_action : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ p : Coordinates F,
      KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (toArch F p) =
        toArch F (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p)
  unipotent_action : ∀ (x : D.L) (p : Coordinates F),
    KPCuspSiegel.action F
      (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F ((p.1.1 + embedding F (x : F), p.1.2), p.2)
  shapeMeasure : Measure (Shape F)
  haar_shapeMeasure : shapeMeasure.IsAddHaarMeasure
  archVolume_formula :
    Measure.map (toArch F)
      ((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  measure_invariant : ∀ g : S,
    Measure.map (crossAction g) (volume.prod shapeMeasure) = volume.prod shapeMeasure
  fundamentalDomain : Set (Cross F)
  measurable_fundamentalDomain : MeasurableSet fundamentalDomain
  isFundamentalDomain :
    letI := homeomorphAction crossAction
    IsFundamentalDomain S fundamentalDomain (volume.prod shapeMeasure)
  sectionMeasure : Measure (CrossQuotient F S)
  sectionMeasure_formula : sectionMeasure = Measure.map (Quotient.mk (crossRelation F S))
    ((volume.prod shapeMeasure).restrict fundamentalDomain)
  finite_sectionMeasure : IsFiniteMeasure sectionMeasure
  positive_sectionMeasure : sectionMeasure Set.univ ≠ 0

  radialPresentation : CrossQuotient F S × ℝ ≃ₜ TotalQuotient F S
  radialPresentation_formula : ∀ (p : Cross F) (t : ℝ),
    radialPresentation (Quotient.mk _ p, t) = Quotient.mk _ (p, t)

  quotientVolume_formula :
    Measure.map radialPresentation
      (sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) =
    Measure.map (Quotient.mk (totalRelation F S))
      (((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : Coordinates F | p.1 ∈ fundamentalDomain})
  highPresentation : ∀ T : ℝ,
    CrossQuotient F S × Set.Ioi T ≃ₜ HighQuotient F S T
  highPresentation_formula : ∀ (T : ℝ) (p : Cross F) (t : Set.Ioi T),
    highPresentation T (Quotient.mk _ p, t) = Quotient.mk _ ⟨(p, t.val), t.property⟩

  highVolume_formula : ∀ T : ℝ,
    Measure.map (highPresentation T)
      (sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) =
    Measure.map (Quotient.mk (highRelation F S T))
      (Measure.comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F)
        (((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : Coordinates F | p.1 ∈ fundamentalDomain}))

theorem affine_radial (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p : Coordinates F) :
    (affine F hF E hE u v p).2 = p.2 := rfl

theorem toArch_contDiff (F : Type*) [Field F] [NumberField F] :
    ContDiff ℝ ⊤ (toArch F) := by
  have hb : ContDiff ℝ ⊤ (fun p : Coordinates F =>
      (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ)) :=
    (Shape F).subtypeL.contDiff.comp (contDiff_snd.comp contDiff_fst)
  unfold toArch
  apply contDiff_pi.mpr
  intro i
  exact (by fun_prop : ContDiff ℝ ⊤ (fun p : Coordinates F => p.1.1 i)).prodMk
    (contDiff_snd.add ((contDiff_apply ℝ ℝ i).comp hb))

 theorem upper_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hc : g 1 0 = 0) (u : ℂ) (hu : u ≠ 0) (ha : g 0 0 = u * g 1 1)
    (z : KPArch.H3) :
    KPArch.action g z = (u * z.1 + g 0 1 / g 1 1, z.2 + Real.log ‖u‖) := by
  have hd : g 1 1 ≠ 0 := by
    intro h
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hdR : ‖g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have huR : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  apply Prod.ext
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), star_zero, mul_zero, add_zero]
    have hn : (‖g 1 1‖ ^ 2 : ℝ) = (g 1 1 * star (g 1 1) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (g 1 1)).symm
    rw [hn, ha]
    have hds : star (g 1 1) ≠ 0 := star_ne_zero.mpr hd
    field_simp
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
      Matrix.det_fin_two, sub_zero, ha, norm_mul]
    have he : ‖u‖ * ‖g 1 1‖ * ‖g 1 1‖ * KPArch.height z / ‖g 1 1‖ ^ 2 =
        ‖u‖ * KPArch.height z := by field_simp
    rw [he, KPArch.height, Real.log_mul huR (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring

theorem actual_affine_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Coordinates F) :
    KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p) := by
  rw [← hA, KPCuspSiegel.action_mk]
  funext i
  let σ := (KPCusp.complexPlace F i).embedding
  have hi : (Matrix.GeneralLinearGroup.map σ A) 1 0 = 0 := by
    change σ (A 1 0) = 0
    simp [hc]
  have hu : σ ((D.ratio g : Fˣ) : F) ≠ 0 :=
    (map_ne_zero σ).mpr (Units.ne_zero _)
  have ha : (Matrix.GeneralLinearGroup.map σ A) 0 0 =
      σ ((D.ratio g : Fˣ) : F) * (Matrix.GeneralLinearGroup.map σ A) 1 1 := by
    change σ (A 0 0) = _
    rw [D.ratioFormula g A hA hc, map_mul]
    rfl
  change KPArch.action (Matrix.GeneralLinearGroup.map σ A) (toArch F p i) = _
  rw [upper_action _ hi _ hu ha]
  apply Prod.ext
  · change σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1) / σ (A 1 1) =
      σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1 / A 1 1)
    rw [map_div₀]
  · change p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i + Real.log ‖σ _‖ =
      p.2 + ((p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((D.ratio g : Fˣ) : F)))
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    ring

theorem actual_unipotent_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (x : D.L) (p : Coordinates F) :
    KPCuspSiegel.action F
      (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F ((p.1.1 + embedding F (x : F), p.1.2), p.2) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F)
  obtain ⟨hc, ha, hb⟩ := D.unipotentFormula x A hA
  have hd : A 1 1 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hr : D.ratio (D.inclusion (Multiplicative.ofAdd x)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← D.exact]
    exact ⟨_, rfl⟩
  rw [actual_affine_action F hF S D _ A hA hc p, hr]
  have hv : A 0 1 / A 1 1 = (x : F) := by rw [hb, ha, mul_div_cancel_right₀ _ hd]
  rw [hv]
  congr 1
  ext i <;> simp [affine, embedding]

 theorem shape_sum_zero (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z ∈ Shape F := by
  have hn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  change ∑ i, ((z i).2 - KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) = 0
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, KPCuspLogShape.meanHeight]
  field_simp
  ring

def toArchHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) :
    Coordinates F ≃ₜ KPArch.Space (KPCuspLogShape.dimension F) where
  toFun := toArch F
  invFun z := ((fun i => (z i).1,
    ⟨KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z,
      shape_sum_zero F hd z⟩), KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z)
  left_inv p := by
    have ht := toArch_meanHeight F hd p
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        funext i
        change (toArch F p i).2 - _ = _
        rw [ht]
        simp [toArch]
    · exact ht
  right_inv z := by
    funext i
    apply Prod.ext
    · rfl
    · change _ + ((z i).2 - _) = (z i).2
      ring
  continuous_toFun := (toArch_contDiff F).continuous
  continuous_invFun := by
    have ht : Continuous (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)) := by
      unfold KPCuspLogShape.meanHeight
      fun_prop
    have hb : Continuous (KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F)) := by
      unfold KPCuspLogShape.shapeCoordinates
      fun_prop
    exact (by fun_prop : Continuous (fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
      fun i => (z i).1)).prodMk (hb.subtype_mk (shape_sum_zero F hd)) |>.prodMk ht

def projectiveHomeomorph (F : Type*) [Field F] [NumberField F]
    (g : KPCuspArithmetic.PGL2 F) :
    KPArch.Space (KPCuspLogShape.dimension F) ≃ₜ KPArch.Space (KPCuspLogShape.dimension F) where
  toFun := KPCuspSiegel.action F g
  invFun := KPCuspSiegel.action F g⁻¹
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  continuous_toFun := by
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have he : KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) = KPCuspSiegel.glAction F A := by
      funext z; exact KPCuspSiegel.action_mk F A z
    rw [he]
    exact (KPArch.productAction_contDiff _ _).continuous
  continuous_invFun := by
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g⁻¹
    have he : KPCuspSiegel.action F g⁻¹ = KPCuspSiegel.glAction F A := by
      funext z; rw [← hA]; exact KPCuspSiegel.action_mk F A z
    rw [he]
    exact (KPArch.productAction_contDiff _ _).continuous

def highCoordinatesHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    {p : Coordinates F // T < p.2} ≃ₜ KPCuspSiegel.highCusp F σ T :=
  ((toArchHomeomorph F hd).subtype (fun p => by
    change T < p.2 ↔ T < KPCuspLogShape.meanHeight _ (toArch F p)
    rw [toArch_meanHeight F hd])).trans
    ((projectiveHomeomorph F σ).image {z | T < KPCuspLogShape.meanHeight _ z})

 theorem conjugated_orbit_iff (F : Type*) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (z w : KPArch.Space (KPCuspLogShape.dimension F)) :
    MulAction.orbitRel (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) _ z w ↔
    MulAction.orbitRel (KPCuspSiegel.parabolic F Γ q) _ (σ • z) (σ • w) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.property
    refine ⟨⟨k, hk⟩, ?_⟩
    have hkg' : σ⁻¹ * k * σ = (g : KPCuspArithmetic.PGL2 F) := by
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using hkg
    change k • (σ • w) = σ • z
    rw [← hg]
    change k • (σ • w) = σ • ((g : KPCuspArithmetic.PGL2 F) • w)
    rw [← hkg']
    simp only [mul_smul, smul_inv_smul]
  · rintro ⟨k, hk⟩
    let g : KPCuspArithmetic.conjugatedStabilizer F Γ q σ :=
      ⟨σ⁻¹ * (k : KPCuspArithmetic.PGL2 F) * σ,
        Subgroup.mem_map.mpr ⟨k.val, k.property, by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]⟩⟩
    refine ⟨g, ?_⟩
    change (σ⁻¹ * (k : KPCuspArithmetic.PGL2 F) * σ) • w = z
    change (k : KPCuspArithmetic.PGL2 F) • (σ • w) = σ • z at hk
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun v => σ⁻¹ • v) hk

def highCuspQuotientHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    HighQuotient F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T ≃ₜ
      KPCuspSiegel.CuspQuotient F Γ q (KPCuspSiegel.highCusp F σ T) :=
  Homeomorph.Quotient.congr (highCoordinatesHomeomorph F hd σ T) (fun p r =>
    conjugated_orbit_iff F Γ q σ (toArch F p.val) (toArch F r.val))

theorem highCuspQuotientHomeomorph_formula (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (p : {p : Coordinates F // T < p.2}) :
    ∃ z : KPCuspSiegel.highCusp F σ T,
      z.val = KPCuspSiegel.action F σ (toArch F p.val) ∧
      highCuspQuotientHomeomorph F hd Γ q σ T (Quotient.mk _ p) = Quotient.mk _ z := by
  exact ⟨highCoordinatesHomeomorph F hd σ T p, rfl, rfl⟩

theorem positive_dimension (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    0 < KPCuspLogShape.dimension F := by
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hp : 0 < Module.finrank ℚ F := Module.finrank_pos
  change 0 < NumberField.InfinitePlace.nrComplexPlaces F
  omega

theorem chartOutput_nonempty
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : ParabolicData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule) :
    Nonempty (ChartOutput F hF S D) := by
  obtain ⟨G⟩ := KPCuspChart.finite_affine_bundle_atlas F hF S D hdisc hlattice
  obtain ⟨V⟩ := KPCuspChart.normalized_finite_section F hF S D hdisc hlattice G
  obtain ⟨R⟩ := KPCuspChart.radial_quotient_disintegration F hF S D G V
  exact ⟨{
    toGeometryData := G
    positive_dimension := positive_dimension F hF
    lattice := ⟨hdisc, hlattice⟩
    actual_action := actual_affine_action F hF S D
    unipotent_action := actual_unipotent_action F hF S D
    shapeMeasure := V.shapeMeasure
    haar_shapeMeasure := V.haar_shapeMeasure
    archVolume_formula := V.archVolume_formula
    measure_invariant := V.measure_invariant
    fundamentalDomain := V.fundamentalDomain
    measurable_fundamentalDomain := V.measurable_fundamentalDomain
    isFundamentalDomain := V.isFundamentalDomain
    sectionMeasure := V.sectionMeasure
    sectionMeasure_formula := V.sectionMeasure_formula
    finite_sectionMeasure := V.finite_sectionMeasure
    positive_sectionMeasure := V.positive_sectionMeasure
    radialPresentation := R.radialPresentation
    radialPresentation_formula := R.radialPresentation_formula
    quotientVolume_formula := R.quotientVolume_formula
    highPresentation := R.highPresentation
    highPresentation_formula := R.highPresentation_formula
    highVolume_formula := R.highVolume_formula
  }⟩

end KPCuspCharts

theorem kp_cusp_equivariant_nilmanifold_charts
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    ∃ D : KPCuspCharts.ParabolicData F S, Nonempty (KPCuspCharts.ChartOutput F hF S D) := by
  obtain ⟨D, hdisc, hlattice⟩ := KPCuspChart.arithmetic_extension_lattice
    F hF M hM Γ hΓ hcomm q σ hσ
  exact ⟨D, KPCuspCharts.chartOutput_nonempty F hF _ D hdisc hlattice⟩

end DedekindZetaZeroFree

end
