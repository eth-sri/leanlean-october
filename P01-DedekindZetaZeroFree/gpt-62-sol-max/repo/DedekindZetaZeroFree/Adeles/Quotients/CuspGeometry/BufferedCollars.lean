module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspCutoffBoundaryVanishing
public import DedekindZetaZeroFree.Geometry.Cusps.EmbeddedEndsAndCompactCollars
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCollarBuffer

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaar.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Base := KPFiniteCuspAtlas.rawXU F ζ hζ U

abbrev Covered := KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U

abbrev CuspIndex := Σ i : Fin (H.atlas U).componentCount,
  Fin ((H.atlas U).cuspAtlas i).cuspCount

abbrev Stabilizer (a : CuspIndex F ζ hζ U R P H) :=
  KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
    (((H.atlas U).cuspAtlas a.1).cusp a.2)
    (((H.atlas U).cuspAtlas a.1).representative a.2)

def chartLift (a : CuspIndex F ζ hζ U R P H)
    (z : KPCuspCharts.Coordinates F) : Base F ζ hζ U :=
  Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
    ((((H.atlas U).cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z),
      (H.atlas U).representative a.1)

def endSet (τ : ℝ) (a : CuspIndex F ζ hζ U R P H) : Set (Base F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
      (((H.atlas U).cuspAtlas a.1).representative a.2) τ

def endChart (τ : ℝ) (a : CuspIndex F ζ hζ U R P H) :
    KPCuspCharts.HighQuotient F (Stabilizer F ζ hζ U R P H a) τ → Base F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.1) ∘
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
      (((H.atlas U).cuspAtlas a.1).cusp a.2)
      (((H.atlas U).cuspAtlas a.1).representative a.2) τ

def height (τ : ℝ) (a : CuspIndex F ζ hζ U R P H)
    (x : Base F ζ hζ U) : ℝ :=
  if h : ∃ z : KPCuspCharts.Coordinates F,
      τ < z.2 ∧ chartLift F ζ hζ U R P H a z = x
  then (Classical.choose h).2 else 0

def zeroExtension (τ : ℝ) (a : CuspIndex F ζ hζ U R P H)
    (f : ℝ → ℝ) : Base F ζ hζ U → ℝ :=
  (endSet F ζ hζ U R P H τ a).indicator
    (fun x => f (height F ζ hζ U R P H τ a x))

def collars (τ T : ℝ) : Set (Base F ζ hζ U) :=
  KPCutoffSource.closedCollars (endSet F ζ hζ U R P H τ)
    (height F ζ hζ U R P H τ) T

def coveredCollars (τ T : ℝ) : Set (Covered F ζ hζ U) :=
  KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' collars F ζ hζ U R P H τ T

theorem endChart_continuous (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    Continuous (KPContActualCollarBuffer.endChart F ζ hζ U R P H τ c) := by
  apply Continuous.comp _ (show Continuous (KPFiniteCuspAtlas.endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
    (((H.atlas U).cuspAtlas c.1).cusp c.2)
    (((H.atlas U).cuspAtlas c.1).representative c.2) τ) from ?_)
  · have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := c.1))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  · apply Continuous.quotient_lift
    have hact : Continuous (KPCuspSiegel.action F (((H.atlas U).cuspAtlas c.1).representative c.2)) :=
      (by unfold KPCuspSiegel.action KPCuspSiegel.glAction
          exact (KPArch.productAction_contDiff _ _).continuous)
    exact continuous_quotient_mk'.comp
      (hact.comp ((KPCuspCharts.toArch_contDiff F).continuous.comp continuous_subtype_val))

theorem compact_slab (c : CuspIndex F ζ hζ U R P H) (L B : ℝ) :
    ∃ K : Set (Base F ζ hζ U), IsCompact K ∧
      ∀ z : KPCuspCharts.Coordinates F, z.2 ∈ Set.Icc L B →
        KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z ∈ K := by
  let G := ((H.atlas U).cuspAtlas c.1).geometry c.2
  let S := KPContActualCollarBuffer.Stabilizer F ζ hζ U R P H c
  letI : CompactSpace (KPCuspCharts.CrossQuotient F S) := G.compact_cross
  letI : CompactSpace (Set.Icc L B) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : KPCuspCharts.CrossQuotient F S × Set.Icc L B → Base F ζ hζ U := fun p =>
    KPContActualCollarBuffer.endChart F ζ hζ U R P H (L-1) c
      (G.highPresentation (L-1) (p.1, ⟨p.2.val, by change L-1 < p.2.val; have := p.2.property.1; linarith⟩))
  have hf : Continuous f := (endChart_continuous F ζ hζ U R P H (L-1) c).comp
    ((G.highPresentation (L-1)).continuous.comp (by fun_prop))
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro z hz
  refine ⟨(Quotient.mk _ z.1, ⟨z.2,hz⟩), ?_⟩
  dsimp only [f]
  rw [G.highPresentation_formula]
  rfl

theorem end_lift_range (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    KPContActualCollarBuffer.chartLift F ζ hζ U R P H c ''
      {z : KPCuspCharts.Coordinates F | τ < z.2} =
    KPContActualCollarBuffer.endSet F ζ hζ U R P H τ c :=
  KPActualCollarBuffer.chartLift_range (H.atlas U) τ c

theorem all_ends_open (t : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    IsOpen (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c) :=
  KPActualCollarBuffer.end_open (H.atlas U) t c

theorem compact_truncated_core (B : ℝ) :
    IsCompact ((⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ) := by
  classical
  choose K hK hslab using (fun c : CuspIndex F ζ hζ U R P H =>
    compact_slab F ζ hζ U R P H c (H.atlas U).threshold B)
  let core := (⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c)ᶜ
  have hc : IsCompact core := by
    convert (H.atlas U).compact_core using 1
    ext x
    simp only [core, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_univ,
      true_and, KPContActualCollarBuffer.endSet]
    simp only [Sigma.exists]
  have hcompact : IsCompact (core ∪ ⋃ c, K c) := hc.union (isCompact_iUnion hK)
  apply hcompact.of_isClosed_subset
  · exact (isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl
  · intro x hx
    by_cases hcore : x ∈ core
    · exact Or.inl hcore
    · right
      have hh : x ∈ ⋃ c : CuspIndex F ζ hζ U R P H,
          KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c :=
        not_not.mp hcore
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
      rw [← end_lift_range F ζ hζ U R P H (H.atlas U).threshold c] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      have hzB : z.2 ≤ B := by
        by_contra hn
        apply hx
        exact Set.mem_iUnion.mpr ⟨c, by rw [← end_lift_range F ζ hζ U R P H B c]; exact ⟨z,lt_of_not_ge hn,rfl⟩⟩
      exact Set.mem_iUnion.mpr ⟨c,hslab c z ⟨hz.le,hzB⟩⟩

structure CollarBuffer (T : ℝ) where
  τ : ℝ
  chart_threshold_le : (H.atlas U).threshold ≤ τ
  below_cutoff : τ < T
  dimension_formula : KPCuspLogShape.dimension F = Module.finrank ℚ F / 2
  positive_dimension : 0 < KPCuspLogShape.dimension F
  open_ends : ∀ a, IsOpen (endSet F ζ hζ U R P H τ a)
  disjoint_ends : Pairwise (fun a b => Disjoint
    (endSet F ζ hζ U R P H τ a) (endSet F ζ hζ U R P H τ b))
  lift_range : ∀ a, chartLift F ζ hζ U R P H a ''
    {z : KPCuspCharts.Coordinates F | τ < z.2} = endSet F ζ hζ U R P H τ a

  height_coordinates : ∀ a (z : KPCuspCharts.Coordinates F), τ < z.2 →
    height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z) = z.2
  height_continuous : ∀ a,
    ContinuousOn (height F ζ hζ U R P H τ a) (endSet F ζ hζ U R P H τ a)
  compact_collars : IsCompact (collars F ζ hζ U R P H τ T)
  compact_covered_collars : IsCompact (coveredCollars F ζ hζ U R P H τ T)
  finite_covered_measure :
    KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U
      (coveredCollars F ζ hζ U R P H τ T) < (⊤ : ℝ≥0∞)

  boundary_height_buffer : ∀ a x, x ∈ frontier (endSet F ζ hζ U R P H τ a) →
    ∃ V : Set (Base F ζ hζ U), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ endSet F ζ hζ U R P H τ a →
        height F ζ hζ U R P H τ a y < T

  boundary_zero_extension : ∀ a x,
    x ∈ frontier (endSet F ζ hζ U R P H τ a) →
    ∃ V : Set (Base F ζ hζ U), IsOpen V ∧ x ∈ V ∧
      ∀ (χ : KPCutoffSource.SmoothCuspCutoff T) y, y ∈ V →
        zeroExtension F ζ hζ U R P H τ a χ.toFun y = 0 ∧
        zeroExtension F ζ hζ U R P H τ a (deriv χ.toFun) y = 0 ∧
        zeroExtension F ζ hζ U R P H τ a (deriv (deriv χ.toFun)) y = 0

end DedekindZetaZeroFree.KPContActualCollarBuffer

namespace DedekindZetaZeroFree

theorem kp_cont_actual_collar_buffer
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (T : ℝ) (hT : (H.atlas U).threshold < T) :
    Nonempty (KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H T) := by
  let τ := ((H.atlas U).threshold + T) / 2
  have hτ : (H.atlas U).threshold ≤ τ := by dsimp [τ]; linarith
  have hτT : τ < T := by dsimp [τ]; linarith
  obtain ⟨hlift, hcoord, hcont⟩ :=
    KPActualCollarBuffer.actual_height_descent F ζ hζ H.totallyComplex U
      (H.atlas U) τ hτ
  obtain ⟨hopen, hdisj, hcompact⟩ :=
    KPActualCollarBuffer.actual_end_charts_compact_collars F ζ hζ
      H.totallyComplex U (H.atlas U) τ T hτ hτT
  obtain ⟨hbuffer, hzero⟩ :=
    KPActualCollarBuffer.actual_boundary_zero_buffer F ζ hζ
      H.totallyComplex U (H.atlas U) τ T hτ hτT
  have hcovered : IsCompact
      (KPContActualCollarBuffer.coveredCollars F ζ hζ U R P H τ T) :=
    (KPContSectorSmoothFramesSupport.q_closed_and_proper F ζ hζ U).2 _ hcompact
  have hmeasure : KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U
      (KPContActualCollarBuffer.coveredCollars F ζ hζ U R P H τ T) < (⊤ : ℝ≥0∞) := by
    letI := KPContSectorFixedMeasureLocalFiniteness.coveredMeasure_finiteOnCompacts
      F ζ hζ R U
    exact hcovered.measure_lt_top
  have hdim : KPCuspLogShape.dimension F = Module.finrank ℚ F / 2 :=
    (kp_cont_finite_cusp_atlas F ζ hζ U).choose_spec.1
  refine ⟨{ τ := τ
            chart_threshold_le := hτ
            below_cutoff := hτT
            dimension_formula := hdim
            positive_dimension := KPCuspCharts.positive_dimension F H.totallyComplex
            open_ends := hopen
            disjoint_ends := hdisj
            lift_range := hlift
            height_coordinates := hcoord
            height_continuous := hcont
            compact_collars := hcompact
            compact_covered_collars := hcovered
            finite_covered_measure := hmeasure
            boundary_height_buffer := hbuffer
            boundary_zero_extension := hzero }⟩

end DedekindZetaZeroFree

end
