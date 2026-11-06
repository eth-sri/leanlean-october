module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas
public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev X := KPFiniteCuspAtlas.rawXU F ζ hζ U

local notation:max "current_X" => X F ζ hζ U

abbrev V := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U

instance : MeasurableSpace (current_X) := borel _


local notation:max "current_Atlas" => KPFiniteCuspAtlas.Atlas F ζ hζ

def quotientMeasure (A : current_Atlas hF U) :
    Measure (current_X) :=
  ∑ i : Fin A.componentCount,
    Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        (A.cuspAtlas i).fundamentalDomain)

abbrev Line (A : current_Atlas hF U) :=
  Σ i : Fin A.componentCount, KPCuspGenuineMonodromy.OrbifoldLine F ζ hζ U
    (A.representative i) (A.line i).rho

def lineBase (A : current_Atlas hF U) :
    Line F ζ hζ hF U A → current_X := fun p =>
  Quotient.lift (fun q => KPFiniteCuspAtlas.componentMap F ζ hζ U
    (A.representative p.1) (KPCuspSiegel.projection F _ q.1)) (by
      intro q q' h
      obtain ⟨γ, hbase, _⟩ := h
      rw [hbase]
      apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative p.1))
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, by
        change γ⁻¹ • (γ • q.1) = q.1
        simp⟩) p.2

structure Realization (A : current_Atlas hF U) where
  component : current_X → Fin A.componentCount
  lift : current_X → KPFiniteCuspAtlas.SymmetricSpace F
  measurable_component : Measurable component
  measurable_lift : Measurable lift
  lift_formula : ∀ x, KPFiniteCuspAtlas.componentMap F ζ hζ U
    (A.representative (component x))
    (KPCuspSiegel.projection F _ (lift x)) = x
  lift_in_domain : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    lift x ∈ (A.cuspAtlas (component x)).fundamentalDomain
  free_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative (component x)),
      (γ : KPCuspArithmetic.PGL2 F) • lift x = lift x → γ = 1

  representative : KPFiniteCuspAtlas.genuineScalars F ζ hζ U →ₗ[ℂ]
    (current_X → V F ζ hζ U)
  section_formula : ∀ s x, (representative s x : ℂ) =
    s.val (lift x, A.representative (component x))

  frame : (x : current_X) → V F ζ hζ U → Line F ζ hζ hF U A
  frame_formula : ∀ x a, frame x a =
    ⟨component x, Quotient.mk _ (lift x, a)⟩
  frame_base : ∀ x a, lineBase F ζ hζ hF U A (frame x a) = x
  frame_injective_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    Function.Injective (frame x)
  frame_surjective_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    ∀ l : Line F ζ hζ hF U A, lineBase F ζ hζ hF U A l = x →
      ∃ a, frame x a = l

  smooth_test_memLp : ∀ s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U,
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) →
    HasCompactSupport (representative s) →
    MemLp (representative s) 2 (quotientMeasure F ζ hζ hF U A)

abbrev H (A : current_Atlas hF U) :=
  Lp (V F ζ hζ U) 2 (quotientMeasure F ζ hζ hF U A)

abbrev HK (A : current_Atlas hF U) (K : Set (current_X)) :=
  Lp (V F ζ hζ U) 2 ((quotientMeasure F ζ hζ hF U A).restrict K)

def core (A : current_Atlas hF U)
    (M : Realization F ζ hζ hF U A) : Set (H F ζ hζ hF U A) :=
  {v | ∃ s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U,
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) ∧
    HasCompactSupport (M.representative s) ∧
    (v : current_X → V F ζ hζ U) =ᵐ[quotientMeasure F ζ hζ hF U A]
      M.representative s}

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (a : ℝ) : Set (E n) := {x | ∀ j, -a ≤ x j ∧ x j ≤ a}

structure Chart (A : current_Atlas hF U) where
  n : ℕ
  positive_n : 0 < n
  dimension : n = 3 * KPCuspLogShape.dimension F
  a : ℝ
  positive_a : 0 < a
  radius : ℝ
  positive_radius : 0 < radius
  closed_ball_in_cube : closure (Metric.ball (0 : E n) radius) ⊆ interior (cube n a)
  component : Fin A.componentCount
  center : KPFiniteCuspAtlas.SymmetricSpace F
  finite_stabilizer : Fintype (MulAction.stabilizer
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative component)) center)
  orthogonal : MulAction.stabilizer
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative component)) center →*
      (E n ≃ₗᵢ[ℝ] E n)
  extendedDomain : Set (E n)
  open_extendedDomain : IsOpen extendedDomain
  closed_ball_in_extension : closure (Metric.ball (0 : E n) radius) ⊆ extendedDomain
  invariant_extension : ∀ g, orthogonal g '' extendedDomain = extendedDomain
  coordinates : E n → KPFiniteCuspAtlas.SymmetricSpace F
  coordinates_center : coordinates 0 = center
  smooth_coordinates : ContDiffOn ℝ (⊤ : ℕ∞) coordinates extendedDomain
  coordinates_embedding : Topology.IsEmbedding (Set.restrict extendedDomain coordinates)
  coordinates_open : IsOpen (coordinates '' extendedDomain)
  smooth_inverse : ∃ inv : KPFiniteCuspAtlas.SymmetricSpace F → E n,
    ContDiffOn ℝ (⊤ : ℕ∞) inv (coordinates '' extendedDomain) ∧
    (∀ x ∈ extendedDomain, inv (coordinates x) = x)
  equivariance : ∀ g x, x ∈ extendedDomain →
    coordinates (orthogonal g x) =
      ((g.val : KPCuspArithmetic.PGL2 F) • coordinates x)

  separated : ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative component), ∀ x y,
    x ∈ extendedDomain → y ∈ extendedDomain →
    (γ : KPCuspArithmetic.PGL2 F) • coordinates x = coordinates y →
      γ ∈ MulAction.stabilizer _ center
  weight : E n → ℝ
  smooth_weight : ContDiffOn ℝ (⊤ : ℕ∞) weight extendedDomain
  invariant_weight : ∀ g x, x ∈ extendedDomain → weight (orthogonal g x) = weight x
  lower : ℝ
  upper : ℝ
  positive_lower : 0 < lower
  finite_bounds : ∀ x ∈ closure (Metric.ball (0 : E n) radius),
    lower ≤ weight x ∧ weight x ≤ upper

  coordinate_volume : Measure.map coordinates
    ((volume.restrict (Metric.ball (0 : E n) radius)).withDensity
      (fun x => ENNReal.ofReal (weight x))) =
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
      (coordinates '' Metric.ball (0 : E n) radius)

attribute [instance] Chart.finite_stabilizer

abbrev Chart.G {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) :=
  MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U
    (A.representative C.component)) C.center

def Chart.rho {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) : C.G F ζ hζ hF U →* ℂˣ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ).comp
    ((A.line C.component).rho.comp (MulAction.stabilizer _ C.center).subtype)

def Chart.toBase {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : current_X :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
    (KPCuspSiegel.projection F _ (C.coordinates x))

def Chart.toLine {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) (a : V F ζ hζ U) :
    Line F ζ hζ hF U A :=
  ⟨C.component, Quotient.mk _ (C.coordinates x, a)⟩

def Chart.O {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) : Set (current_X) :=
  C.toBase F ζ hζ hF U '' Metric.ball 0 C.radius

def Chart.average {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) (f : E C.n → ℂ) : E C.n → ℂ :=
  (Metric.ball 0 C.radius).indicator (fun x =>
    (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ *
      ∑ g : C.G F ζ hζ hF U, ((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) *
        f (C.orthogonal g x))

def Chart.metricMatrix {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  fun j k =>
    (KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single k 1))) / 2

def Chart.energyMatrix {A : current_Atlas hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  (C.metricMatrix F ζ hζ hF U x)⁻¹

structure FiniteCutoffs (A : current_Atlas hF U)
    (K : Set (current_X)) where
  count : ℕ
  empty_case : K = ∅ → count = 0
  chart : Fin count → Chart F ζ hζ hF U A

  chart_measure : ∀ i, Measure.map ((chart i).toBase F ζ hζ hF U)
    ((Fintype.card ((chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball 0 (chart i).radius)).withDensity
        (fun x => ENNReal.ofReal ((chart i).weight x))) =
    (quotientMeasure F ζ hζ hF U A).restrict ((chart i).O F ζ hζ hF U)
  ellipticity : Fin count → ℝ
  positive_ellipticity : ∀ i, 0 < ellipticity i
  uniform_ellipticity : ∀ i x, x ∈ closure (Metric.ball (0 : E (chart i).n) (chart i).radius) →
    ∀ ξ : E (chart i).n,
      ellipticity i * ‖ξ‖ ^ 2 ≤
        ∑ j, ∑ k, (chart i).energyMatrix F ζ hζ hF U x j k * ξ j * ξ k
  phi : Fin count → current_X → ℝ
  nonnegative_phi : ∀ i x, 0 ≤ phi i x
  compact_phi : ∀ i, HasCompactSupport (phi i)
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ hF U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun z => phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (current_X)
  open_neighborhood : IsOpen neighborhood
  covers_compact : K ⊆ neighborhood
  partition : ∀ x ∈ neighborhood, ∑ i, phi i x = 1

  cutoff : ∀ i, E (chart i).n → ℝ
  cutoff_formula : ∀ i, cutoff i =
    (Metric.ball 0 (chart i).radius).indicator
      (fun x => phi i ((chart i).toBase F ζ hζ hF U x))
  smooth_cutoff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (cutoff i)
  compact_cutoff : ∀ i, HasCompactSupport (cutoff i)
  support_cutoff : ∀ i, tsupport (cutoff i) ⊆ Metric.ball 0 (chart i).radius
  invariant_cutoff : ∀ i (g : (chart i).G F ζ hζ hF U) x,
    cutoff i ((chart i).orthogonal g x) = cutoff i x

structure FrameComparison (A : current_Atlas hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (current_X)}
    (C : FiniteCutoffs F ζ hζ hF U A K) where
  phase : ∀ i, E (C.chart i).n → ℂˣ
  measurable_phase : ∀ i, Measurable (phase i)
  unitary_phase : ∀ i x, ‖(phase i x : ℂ)‖ = 1
  frame_comparison : ∀ i (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U),
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      s.val ((C.chart i).coordinates x, A.representative (C.chart i).component) =
        (phase i x : ℂ) * (M.representative s ((C.chart i).toBase F ζ hζ hF U x) : ℂ)
  phase_equivariance : ∀ i (g : (C.chart i).G F ζ hζ hF U),
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      (phase i ((C.chart i).orthogonal g x) : ℂ) =
        ((C.chart i).rho F ζ hζ hF U g : ℂ) * (phase i x : ℂ)
  phase_frame : ∀ i,
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      ∀ a : V F ζ hζ U,
        (C.chart i).toLine F ζ hζ hF U x ((phase i x : ℂ) • a) =
          M.frame ((C.chart i).toBase F ζ hζ hF U x) a

structure LocalOperators (A : current_Atlas hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (current_X)}
    (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C) where
  T : ∀ i, H F ζ hζ hF U A →L[ℂ]
    Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))
  T_formula : ∀ i v,
    T i v =ᵐ[volume.restrict (cube (C.chart i).n (C.chart i).a)]
      (Metric.ball 0 (C.chart i).radius).indicator (fun x =>
        (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
          (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))
  R : ∀ i, Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
    HK F ζ hζ hF U A K

  R_formula : ∀ i f,
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      (C.chart i).toBase F ζ hζ hF U x ∈ K →
      R i f ((C.chart i).toBase F ζ hζ hF U x) =
        (V F ζ hζ U).orthogonalProjectionOnto
          (((P.phase i x)⁻¹ : ℂˣ) * (C.chart i).average F ζ hζ hF U f x)
  R_zero_extension : ∀ i f,
    ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict K,
      x ∉ (C.chart i).O F ζ hζ hF U → R i f x = 0
  smooth_core_image : ∀ i v, v ∈ core F ζ hζ hF U A M →
    ∃ f : E (C.chart i).n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ interior (cube (C.chart i).n (C.chart i).a) ∧
      T i v =ᵐ[volume.restrict (cube (C.chart i).n (C.chart i).a)] f

end DedekindZetaZeroFree.CoreChartLocalizers

end
