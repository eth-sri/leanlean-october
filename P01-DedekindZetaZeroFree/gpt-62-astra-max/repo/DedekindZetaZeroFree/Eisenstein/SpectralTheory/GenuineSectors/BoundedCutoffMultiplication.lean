module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CutoffMultipliers

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorMultiplier

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentPieceHilbertSum
open KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]
private theorem continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs
private theorem continuous_of_all_lifts (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hf : ∀ a : ActualChart (U := U) (H := H), Continuous (fun y : omega a => f (q a y.val))) :
    Continuous f := by
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (by rw [cover.covers]; trivial)
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    let a := cover.chart n
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_iff_isQuotientMap (cover.properties n).quotient _).mpr ?_
    convert (hf a).comp (coordinates_continuous a) using 1
    funext y
    exact congrArg f (q_coordinates a y).symm
private theorem cutoff_continuous (η : RealSmoothCutoff F ζ hζ U R P H) : Continuous η.val := by
  apply continuous_of_all_lifts
  intro a
  obtain ⟨g,hg,he⟩ := η.smooth a
  convert hg.continuousOn.domRestrict using 1
  exact funext (fun y => (he y).symm)
private theorem exists_chart_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  obtain ⟨n,y,hy⟩ := Set.mem_iUnion.mp (by rw [cov.covers]; trivial)
  refine ⟨cov.chart n, coordinates (cov.chart n) y, ?_⟩
  change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (cov.chart n).component)
    (KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ)
      (labeledAInv (placeEquiv F ζ hζ) y.val))) = x
  have hl : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k; simp [labeledA,labeledAInv]
  rw [hl]; exact hy

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorFixedPushforwardSupport KPContSectorClosedLpSubspace
open KPContActualSectorTestEmbeddings
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
 def weight (η : RealSmoothCutoff F ζ hζ U R P H) (x : CoveredSpherical F ζ hζ U) : ℂ :=
  (η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ)

 section

variable (η : RealSmoothCutoff F ζ hζ U R P H) (B : ℝ) (hη : ∀ x, |η.val x| ≤ B)

include hη in
theorem mulMem
    (f : CoveredL2 F ζ hζ R U) : MemLp (fun x => weight η x * f x) 2 (coveredMeasure F ζ hζ R U) := by
  exact (memLp_top_of_bound (((Complex.continuous_ofReal.comp ((cutoff_continuous η).comp
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)))).measurable.aestronglyMeasurable) B (Filter.Eventually.of_forall (fun x => by simpa [weight] using hη (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x)))).mul (Lp.memLp f)
 def mulLinear :
    CoveredL2 F ζ hζ R U →ₗ[ℂ] CoveredL2 F ζ hζ R U where
  toFun f := (mulMem η B hη f).toLp (fun x => weight η x * f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(mulMem η B hη (f+g)).coeFn_toLp,
      (mulMem η B hη f).coeFn_toLp, (mulMem η B hη g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((mulMem η B hη f).toLp _) ((mulMem η B hη g).toLp _)] with x h1 h2 h3 h4 h5
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(mulMem η B hη (c • f)).coeFn_toLp,
      (mulMem η B hη f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((mulMem η B hη f).toLp _)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,h1,h4,Pi.smul_apply,h2,h3,smul_eq_mul,mul_left_comm]

end
 section

variable (η : RealSmoothCutoff F ζ hζ U R P H) (B : ℝ) (hB : 0 ≤ B) (hη : ∀ x, |η.val x| ≤ B)

def mulCLM : CoveredL2 F ζ hζ R U →L[ℂ] CoveredL2 F ζ hζ R U := by
  refine (mulLinear η B hη).mkContinuous B ?_
  intro f
  change ‖(mulMem η B hη f).toLp _‖ ≤ B * ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  let coveredMeasure₀ := coveredMeasure F ζ hζ R U
  have hh : eLpNorm (fun x => weight η x * f x) 2 (coveredMeasure₀) ≤
      ENNReal.ofReal B * eLpNorm f 2 (coveredMeasure₀) := by
    calc _ ≤ eLpNorm (fun x => (B : ℂ) * f x) 2 (coveredMeasure₀) := by
           apply eLpNorm_mono (mulMem η B hη f).aestronglyMeasurable
           intro x
           rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
           apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
           simpa [weight] using hη (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x)
         _ = _ := by
           change eLpNorm ((B : ℂ) • (fun x => f x)) 2 (coveredMeasure₀) = _
           rw [eLpNorm_const_smul, ← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) (Lp.memLp f).eLpNorm_ne_top) hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hr
  exact hr
private theorem mulCLM_ae (f : CoveredL2 F ζ hζ R U) :
    mulCLM η B hB hη f =ᵐ[coveredMeasure F ζ hζ R U] (fun x => weight η x * f x) :=
  (mulMem η B hη f).coeFn_toLp
 theorem mulCLM_mem (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    mulCLM η B hB hη u.val ∈ KPContSectorClosedLpSubspace.H F ζ hζ R U := by
  rw [mem_H_iff]
  intro ε
  have ha := mulCLM_ae η B hB hη u.val
  filter_upwards [ha,((KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).quasiMeasurePreserving.ae ha),((mem_H_iff F ζ hζ R U u.val).mp u.property ε)] with x h1 h2 h3
  change mulCLM η B hB hη u.val (z F ζ hζ U ε x) = (chi F ζ hζ ε : ℂ) * mulCLM η B hB hη u.val x
  rw [h2,h1]
  have hw : weight η (z F ζ hζ U ε x) = weight η x := by rw [weight,weight,q_z]
  change u.val (z F ζ hζ U ε x) = (chi F ζ hζ ε : ℂ) * u.val x at h3
  rw [hw,h3,mul_left_comm]
 def sectorCLM : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (((mulCLM η B hB hη).comp (KPContSectorClosedLpSubspace.H F ζ hζ R U).subtypeL).codRestrict
    (KPContSectorClosedLpSubspace.H F ζ hζ R U) (mulCLM_mem η B hB hη))

end

 def chartCovered (a : ActualChart (U := U) (H := H)) (y : omega a) : CoveredSpherical F ζ hζ U :=
  Quotient.mk (coveredRelation F ζ hζ U) (labeledA (placeEquiv F ζ hζ) y.val, (H.atlas U).representative a.component)

private theorem coveredFields (g : GenuineCoveredScalars F ζ hζ U)
    (a : ActualChart (U := U) (H := H)) (y : omega a) :
    sectionFields (S F ζ hζ U R P H g) a y = g.val (chartCovered a y) := by
  rw [sectionFields, LiftedChart.coefficient]
  simp only [isotropyChart, ChartKind.representative, one_smul, map_one, Complex.ofReal_one, Units.val_one, one_mul]
  exact S_apply F ζ hζ U R P H g a.component _
private theorem scalarCovered_chart (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a) :
    (scalarCovered f).val (chartCovered a y) = f.val a y := by
  rw [← coveredFields, S_scalarCovered]
  exact congrFun (congrFun ((Classical.choose_spec (scalar_gluing f)).1.2.2) a) y
private theorem genuine_eq_of_charts (g h : GenuineCoveredScalars F ζ hζ U)
    (he : ∀ (a : ActualChart (U := U) (H := H)) (y : omega a), g.val (chartCovered a y) = h.val (chartCovered a y)) : g = h := by
  apply Subtype.ext
  funext x
  obtain ⟨a,y,hy⟩ := exists_chart_point (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x)
  obtain ⟨ε,hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U (chartCovered a y) x).mp
    ((rfl).trans hy)
  rw [hε,g.property,h.property,he a y]
 section

variable (η : RealSmoothCutoff F ζ hζ U R P H)

def productCovered (g : GenuineCoveredScalars F ζ hζ U) :
    GenuineCoveredScalars F ζ hζ U :=
  ⟨fun x => weight η x * g.val x, by
    intro ε x
    have hw : weight η (z F ζ hζ U ε x) = weight η x := by rw [weight,weight,q_z]
    change weight η (z F ζ hζ U ε x) * g.val (z F ζ hζ U ε x) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (weight η x * g.val x)
    rw [hw,g.property,mul_left_comm]⟩
private theorem scalarCovered_mul (f : S_U F ζ hζ U R P H) :
    scalarCovered (scalarMultiply η f) = productCovered η (scalarCovered f) := by
  apply genuine_eq_of_charts
  intro a y
  rw [scalarCovered_chart]
  change cutoffLift η a y * f.val a y = weight η (chartCovered a y) * (scalarCovered f).val (chartCovered a y)
  rw [scalarCovered_chart]
  rfl

end
private theorem sectorCLM_test (η : RealSmoothCutoff F ζ hζ U R P H) (B : ℝ) (hB : 0 ≤ B)
    (hη : ∀ x, |η.val x| ≤ B) (f : S_U F ζ hζ U R P H) :
    sectorCLM η B hB hη (iota f) = iota (scalarMultiply η f) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(mulCLM_ae η B hB hη (iota f).val),((scalar_memLp f).coeFn_toLp),((scalar_memLp (scalarMultiply η f)).coeFn_toLp)] with x hx1 hx2 hx3
  change mulCLM η B hB hη (iota f).val x = (iota (scalarMultiply η f)).val x
  rw [hx1]
  change (iota f).val x = (scalarCovered f).val x at hx2
  change (iota (scalarMultiply η f)).val x = (scalarCovered (scalarMultiply η f)).val x at hx3
  rw [hx2,hx3,scalarCovered_mul]
  rfl

theorem boundedSectorMultiplier
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (η : KPContActualSectorTestDifferentialDescent.RealSmoothCutoff F ζ hζ U R P H)
    (B : ℝ) (hB : 0 ≤ B) (hη : ∀ x, |η.val x| ≤ B) :
    Nonempty (KPContActualSquareEndPartition.SectorMultiplier F ζ hζ U R P H η) := by
      refine ⟨{ op := sectorCLM η B hB hη
                ae_apply := ?_
                test_commutes := sectorCLM_test η B hB hη
                 }⟩
      · intro u
        exact mulCLM_ae η B hB hη u.val

end DedekindZetaZeroFree.KPContActualSectorMultiplier

end
