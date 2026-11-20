module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.MeasurableOrthonormalFrames
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.EllipticityAndCutoffs
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.UnitaryFrameComparison
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.PartitionReconstruction

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree
namespace KPCoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev X := KPFiniteCuspAtlas.rawXU F ζ hζ U
abbrev V := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U

instance : MeasurableSpace (X F ζ hζ U) := borel _

section

variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

def quotientMeasure :
    Measure (X F ζ hζ U) :=
  ∑ i : Fin A.componentCount,
    Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        (A.cuspAtlas i).fundamentalDomain)

abbrev Line :=
  Σ i : Fin A.componentCount, KPCuspGenuineMonodromy.OrbifoldLine F ζ hζ U
    (A.representative i) (A.line i).rho

def lineBase :
    Line F ζ hζ hF U A → X F ζ hζ U := fun p =>
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

end

structure Realization (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) where
  representative : KPFiniteCuspAtlas.genuineScalars F ζ hζ U →ₗ[ℂ]
    (X F ζ hζ U → V F ζ hζ U)

abbrev H (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :=
  Lp (V F ζ hζ U) 2 (quotientMeasure F ζ hζ hF U A)

section

variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (K : Set (X F ζ hζ U))

abbrev HK :=
  Lp (V F ζ hζ U) 2 ((quotientMeasure F ζ hζ hF U A).restrict K)

def restriction :
    H F ζ hζ hF U A →L[ℂ] HK F ζ hζ hF U A K :=
  LpToLpRestrictCLM (X F ζ hζ U) (V F ζ hζ U) ℂ
    (quotientMeasure F ζ hζ hF U A) 2 K

theorem restriction_formula (v : H F ζ hζ hF U A) :
    restriction F ζ hζ hF U A K v
      =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict K] v :=
  LpToLpRestrictCLM_coeFn ℂ K v

end

def core (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) : Set (H F ζ hζ hF U A) :=
  {v | ∃ s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U,
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) ∧
    HasCompactSupport (M.representative s) ∧
    (v : X F ζ hζ U → V F ζ hζ U) =ᵐ[quotientMeasure F ζ hζ hF U A]
      M.representative s}

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (a : ℝ) : Set (E n) := {x | ∀ j, -a ≤ x j ∧ x j ≤ a}

structure Chart (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) where
  n : ℕ
  positive_n : 0 < n
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

section

variable {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U} (C : Chart F ζ hζ hF U A)

abbrev Chart.G :=
  MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U
    (A.representative C.component)) C.center

def Chart.rho : C.G F ζ hζ hF U →* ℂˣ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ).comp
    ((A.line C.component).rho.comp (MulAction.stabilizer _ C.center).subtype)

theorem Chart.rho_unitary (g : C.G F ζ hζ hF U) :
    ‖(C.rho F ζ hζ hF U g : ℂ)‖ = 1 := (A.line C.component).unitary _

theorem Chart.section_equivariance
    (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (g : C.G F ζ hζ hF U) {x : E C.n} (hx : x ∈ C.extendedDomain) :
    s.val (C.coordinates (C.orthogonal g x), A.representative C.component) =
      (C.rho F ζ hζ hF U g : ℂ) *
        s.val (C.coordinates x, A.representative C.component) := by
  rw [C.equivariance g x hx]
  simpa only [A.scalar_realization_formula, Chart.rho, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using ((A.scalar_realization s C.component).property.2 g.val (C.coordinates x))

def Chart.toBase (x : E C.n) : X F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
    (KPCuspSiegel.projection F _ (C.coordinates x))

def Chart.toLine (x : E C.n) (a : V F ζ hζ U) :
    Line F ζ hζ hF U A :=
  ⟨C.component, Quotient.mk _ (C.coordinates x, a)⟩

def Chart.lineRelation :
    Setoid (Metric.ball (0 : E C.n) C.radius × V F ζ hζ U) :=
  Setoid.ker (fun p => C.toLine F ζ hζ hF U p.1.val p.2)

def Chart.O : Set (X F ζ hζ U) :=
  C.toBase F ζ hζ hF U '' Metric.ball 0 C.radius

def Chart.relation : Setoid (Metric.ball (0 : E C.n) C.radius) :=
  Setoid.ker (fun x => C.toBase F ζ hζ hF U x.val)

def Chart.average (f : E C.n → ℂ) : E C.n → ℂ :=
  (Metric.ball 0 C.radius).indicator (fun x =>
    (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ *
      ∑ g : C.G F ζ hζ hF U, ((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) *
        f (C.orthogonal g x))

def Chart.metricMatrix (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  fun j k =>
    (KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single k 1))) / 2

def Chart.energyMatrix (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  (C.metricMatrix F ζ hζ hF U x)⁻¹

end

section ChartFacts

variable {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U} (C : Chart F ζ hζ hF U A)
theorem Chart.orthogonal_mem_ball (g : C.G F ζ hζ hF U) (x : E C.n) :
    C.orthogonal g x ∈ Metric.ball 0 C.radius ↔ x ∈ Metric.ball 0 C.radius := by
  simp
section

variable (f : E C.n → ℂ)

theorem Chart.average_eq_self
    (heq : ∀ (g : C.G F ζ hζ hF U) x, x ∈ Metric.ball 0 C.radius →
      f (C.orthogonal g x) = (C.rho F ζ hζ hF U g : ℂ) * f x)
    {x : E C.n} (hx : x ∈ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = f x := by
  rw [Chart.average, Set.indicator_of_mem hx]
  have hs : (∑ g : C.G F ζ hζ hF U,
      (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x)) =
      (Fintype.card (C.G F ζ hζ hF U) : ℂ) * f x := by
    simp [heq _ _ hx, ← mul_assoc]
  rw [hs, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.average_zero_outside
    {x : E C.n} (hx : x ∉ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = 0 := Set.indicator_of_notMem hx _

theorem Chart.average_equivariant
    (h : C.G F ζ hζ hF U) (x : E C.n) :
    C.average F ζ hζ hF U f (C.orthogonal h x) =
      (C.rho F ζ hζ hF U h : ℂ) * C.average F ζ hζ hF U f x := by
  by_cases hx : x ∈ Metric.ball 0 C.radius
  let rho₀ := C.rho F ζ hζ hF U
  · rw [Chart.average, Set.indicator_of_mem ((C.orthogonal_mem_ball F ζ hζ hF U h x).mpr hx),
      Set.indicator_of_mem hx]
    have hs : (∑ g : C.G F ζ hζ hF U,
        (((rho₀ g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g (C.orthogonal h x))) =
        (rho₀ h : ℂ) *
        ∑ g : C.G F ζ hζ hF U,
          (((rho₀ g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_equiv (Equiv.mulRight h)
      intro g
      change (((rho₀ g)⁻¹ : ℂˣ) : ℂ) *
        f (C.orthogonal g (C.orthogonal h x)) =
        (rho₀ h : ℂ) *
          ((((rho₀ (g * h))⁻¹ : ℂˣ) : ℂ) *
            f (C.orthogonal (g * h) x))
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
        mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
      have hn := Units.ne_zero (rho₀ h)
      field_simp
    rw [hs]
    ring
  · rw [C.average_zero_outside F ζ hζ hF U f hx,
      C.average_zero_outside F ζ hζ hF U f
        (fun hh => hx ((C.orthogonal_mem_ball F ζ hζ hF U h x).mp hh)), mul_zero]

end

theorem Chart.invariant_ball :
    ∀ g : C.G F ζ hζ hF U,
      C.orthogonal g '' Metric.ball 0 C.radius = Metric.ball 0 C.radius := by
  intro g
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.orthogonal_mem_ball F ζ hζ hF U g y).mpr hy
  · intro hx
    refine ⟨(C.orthogonal g).symm x, ?_, (C.orthogonal g).apply_symm_apply x⟩
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
      using hx

theorem Chart.toBase_invariant (g : C.G F ζ hζ hF U) (x : E C.n)
    (hx : x ∈ C.extendedDomain) :
    C.toBase F ζ hζ hF U (C.orthogonal g x) = C.toBase F ζ hζ hF U x := by
  unfold Chart.toBase
  rw [C.equivariance g x hx]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component))
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨g.val, rfl⟩

theorem Chart.orbit_relation (x y : Metric.ball (0 : E C.n) C.radius) :
    (C.relation F ζ hζ hF U).r x y ↔
      ∃ g : C.G F ζ hζ hF U, C.orthogonal g x.val = y.val := by
  have hx : x.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure x.property)
  have hy : y.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure y.property)
  constructor
  let Component₀ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)
  · intro h
    change C.toBase F ζ hζ hF U x.val = C.toBase F ζ hζ hF U y.val at h
    have hb : KPCuspSiegel.projection F
        (Component₀)
        (C.coordinates x.val) =
        KPCuspSiegel.projection F
          (Component₀)
          (C.coordinates y.val) := by
      have he := A.components.injective
        ((A.components_formula _ _).trans (h.trans (A.components_formula _ _).symm))
      exact eq_of_heq (Sigma.mk.inj he).2
    have ho := MulAction.orbitRel_apply.mp (Quotient.exact hb)
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp ho
    have hγ' : ((γ⁻¹ : Component₀) : KPCuspArithmetic.PGL2 F) •
        C.coordinates x.val = C.coordinates y.val := by
      change γ⁻¹ • C.coordinates x.val = C.coordinates y.val
      rw [← hγ]
      simp
    have hstab :=
      C.separated γ⁻¹ x.val y.val hx hy hγ'
    let g : C.G F ζ hζ hF U := ⟨γ⁻¹, hstab⟩
    have hgx : C.orthogonal g x.val ∈ C.extendedDomain := by
      rw [← C.invariant_extension g]
      exact ⟨x.val, hx, rfl⟩
    refine ⟨g, ?_⟩
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x.val, hgx⟩)
        (a₂ := ⟨y.val, hy⟩) ?_)
    change C.coordinates (C.orthogonal g x.val) = C.coordinates y.val
    rw [C.equivariance g x.val hx]
    exact hγ'
  · rintro ⟨g, h⟩
    change C.toBase F ζ hζ hF U x.val = C.toBase F ζ hζ hF U y.val
    rw [← h]
    exact (C.toBase_invariant F ζ hζ hF U g x.val hx).symm

theorem Chart.toLine_equivariant (g : C.G F ζ hζ hF U) (x : E C.n)
    (hx : x ∈ C.extendedDomain) (a b : V F ζ hζ U)
    (hab : (b : ℂ) = (C.rho F ζ hζ hF U g : ℂ) * (a : ℂ)) :
    C.toLine F ζ hζ hF U (C.orthogonal g x) b =
      C.toLine F ζ hζ hF U x a := by
  apply congrArg (Sigma.mk C.component)
  apply Eq.symm
  apply Quotient.sound
  exact ⟨g.val, C.equivariance g x hx, hab⟩

theorem Chart.line_orbit_relation (x y : Metric.ball (0 : E C.n) C.radius)
    (a b : V F ζ hζ U) :
    (C.lineRelation F ζ hζ hF U).r (x,a) (y,b) ↔
      ∃ g : C.G F ζ hζ hF U,
        C.orthogonal g x.val = y.val ∧
        (b : ℂ) = (C.rho F ζ hζ hF U g : ℂ) * (a : ℂ) := by
  have hx :=
    C.closed_ball_in_extension (subset_closure x.property)
  have hy :=
    C.closed_ball_in_extension (subset_closure y.property)
  constructor
  · intro h
    change C.toLine F ζ hζ hF U x.val a = C.toLine F ζ hζ hF U y.val b at h
    obtain ⟨γ, hγ, hab⟩ := Quotient.exact (eq_of_heq (Sigma.mk.inj h).2)
    let g : C.G F ζ hζ hF U := ⟨γ, (C.separated γ x.val y.val hx hy hγ.symm)⟩
    refine ⟨g, ?_, hab⟩
    have hgx : C.orthogonal g x.val ∈ C.extendedDomain := by
      rw [← C.invariant_extension g]
      exact ⟨x.val, hx, rfl⟩
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x.val, hgx⟩)
        (a₂ := ⟨y.val, hy⟩) ?_)
    change C.coordinates (C.orthogonal g x.val) = C.coordinates y.val
    rw [C.equivariance g x.val hx]
    exact hγ.symm
  · rintro ⟨g, hxy, hab⟩
    change C.toLine F ζ hζ hF U x.val a = C.toLine F ζ hζ hF U y.val b
    rw [← hxy]
    exact (C.toLine_equivariant F ζ hζ hF U g x.val hx a b hab).symm

theorem Chart.line_chart_surjective (l : Line F ζ hζ hF U A)
    (hl : lineBase F ζ hζ hF U A l ∈ C.O F ζ hζ hF U) :
    ∃ (x : Metric.ball (0 : E C.n) C.radius) (a : V F ζ hζ U),
      C.toLine F ζ hζ hF U x.val a = l := by
  obtain ⟨x, hx, hxl⟩ := hl
  obtain ⟨j, l⟩ := l
  induction l using Quotient.inductionOn with
  | h p =>
    have he : (⟨C.component, KPCuspSiegel.projection F _ (C.coordinates x)⟩ :
        Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) =
        ⟨j, KPCuspSiegel.projection F _ p.1⟩ := by
      apply A.components.injective
      simpa only [A.components_formula, Chart.toBase, lineBase, Quotient.lift_mk] using hxl
    have hj := (Sigma.mk.inj he).1
    subst j
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact (eq_of_heq (Sigma.mk.inj he).2)))
    refine ⟨⟨x, hx⟩, ((KPCuspGenuineMonodromy.chi F ζ hζ ((A.line C.component).rho γ) : ℂ) • p.2), ?_⟩
    apply congrArg (Sigma.mk C.component)
    apply Eq.symm
    apply Quotient.sound
    refine ⟨γ, ?_, rfl⟩
    exact hγ.symm

theorem Chart.coordinates_open_embedding :
    IsOpenEmbedding (Set.restrict C.extendedDomain C.coordinates) := by
  refine ⟨C.coordinates_embedding, ?_⟩
  convert C.coordinates_open using 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
theorem Chart.coordinates_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) C.coordinates) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have ho : IsOpenMap inc := by
    exact (Metric.isOpen_ball.isOpenMap_subtype_val).subtype_mk _
  exact (Chart.coordinates_open_embedding F ζ hζ hF U C).isOpenMap.comp ho
theorem Chart.toBase_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
  have hc : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    simpa only [Function.comp_def, A.components_formula] using (A.components.isOpenMap.comp (isOpenMap_sigmaMk))
  exact hc.comp (isOpenMap_quotient_mk'_mul.comp (Chart.coordinates_ball_open_map F ζ hζ hF U C))
theorem Chart.open_image : IsOpen (C.O F ζ hζ hF U) := by
  convert ((Chart.toBase_ball_open_map F ζ hζ hF U C).isOpen_range) using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
theorem Chart.toBase_ball_continuous :
    Continuous (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    simpa only [Function.comp_def, A.components_formula] using (A.components.continuous.comp (continuous_sigmaMk))
  exact hc.comp (continuous_quot_mk.comp (C.coordinates_embedding.continuous.comp hi))
def Chart.quotientChart : Quotient (C.relation F ζ hζ hF U) ≃ₜ C.O F ζ hζ hF U := by
  let f : Metric.ball (0 : E C.n) C.radius → C.O F ζ hζ hF U :=
    fun x => ⟨C.toBase F ζ hζ hF U x.val, Set.mem_image_of_mem _ x.property⟩
  have hc : Continuous f := (Chart.toBase_ball_continuous F ζ hζ hF U C).subtype_mk _
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have he : C.relation F ζ hζ hF U = Setoid.ker f := by
    ext x y
    change (f x).val = (f y).val ↔ f x = f y
    exact Subtype.ext_iff.symm
  exact (Homeomorph.Quotient.congrRight (fun x y => by rw [he])).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨f, hc⟩) (((Chart.toBase_ball_open_map F ζ hζ hF U C).subtype_mk _).isQuotientMap hc hs))
theorem Chart.quotientChart_formula (x : Metric.ball (0 : E C.n) C.radius) :
    (Chart.quotientChart F ζ hζ hF U C (Quotient.mk _ x)).val =
      C.toBase F ζ hζ hF U x.val := rfl

theorem Chart.measurePreserving_ball (g : C.G F ζ hζ hF U) :
    MeasurePreserving (C.orthogonal g)
      (volume.restrict (Metric.ball (0 : E C.n) C.radius))
      (volume.restrict (Metric.ball (0 : E C.n) C.radius)) := by
  have he : (C.orthogonal g) ⁻¹' Metric.ball (0 : E C.n) C.radius =
      Metric.ball (0 : E C.n) C.radius := by
    ext x
    exact C.orthogonal_mem_ball F ζ hζ hF U g x
  have hm :=
    LinearIsometryEquiv.measurePreserving (C.orthogonal g)
  have hr := hm.restrict_preimage (s := Metric.ball (0 : E C.n) C.radius)
    Metric.isOpen_ball.measurableSet
  rw [he] at hr
  exact hr

def Chart.orthogonalPullback (g : C.G F ζ hζ hF U) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (C.orthogonal g)
    (Chart.measurePreserving_ball F ζ hζ hF U C g)

def Chart.averageLp :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ •
    ∑ g : C.G F ζ hζ hF U, (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap
section

variable (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)))

theorem Chart.norm_averageLp_le :
    ‖Chart.averageLp F ζ hζ hF U C f‖ ≤ ‖f‖ := by
  simp only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ∑ g : C.G F ζ hζ hF U,
          ‖((((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
            (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap f)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ((Fintype.card (C.G F ζ hζ hF U) : ℝ) * ‖f‖) := by
      congr 1
      simp only [norm_smul, Units.val_inv_eq_inv_val, norm_inv,
        C.rho_unitary F ζ hζ hF U, inv_one, one_mul,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ‖f‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.averageLp_formula :
    Chart.averageLp F ζ hζ hF U C f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U f := by
  let b := fun g => (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ)
  let p := fun g : C.G F ζ hζ hF U => Chart.orthogonalPullback F ζ hζ hF U C g f
  have hb : ∀ g, ((b g • p g : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) : E C.n → ℂ)
      =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => b g * f (C.orthogonal g x) := fun g => (Lp.coeFn_smul (b g) (p g)).trans (((fun g =>
      Lp.coeFn_compMeasurePreserving f (Chart.measurePreserving_ball F ζ hζ hF U C g)) g).const_smul (b g))
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun g => b g • p g)
  have hs := hsum.trans (eventuallyEq_sum fun g _ => hb g)
  have hout := (Lp.coeFn_smul (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹
    (∑ g, b g • p g)).trans (hs.const_smul _)
  filter_upwards [hout, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hball
  simpa only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap, Chart.average, Set.indicator_of_mem hball,
    b, p, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hx

end
theorem Chart.average_congr_ae {f k : E C.n → ℂ}
    (hfk : f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)] k) :
    C.average F ζ hζ hF U f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U k := by
  have hg : ∀ g : C.G F ζ hζ hF U,
      (fun x => f (C.orthogonal g x)) =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => k (C.orthogonal g x) := fun g =>
    (Chart.measurePreserving_ball F ζ hζ hF U C g).quasiMeasurePreserving.ae_eq_comp hfk
  filter_upwards [Filter.eventually_all.mpr hg] with x hx
  by_cases hball : x ∈ Metric.ball (0 : E C.n) C.radius
  · simp only [Chart.average, Set.indicator_of_mem hball]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [hx g]
  · simp only [Chart.average, Set.indicator_of_notMem hball]

end ChartFacts

theorem cutoff_derivative_bounds {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ k x, ‖iteratedFDeriv ℝ k f x‖ ≤ B k := by
  choose B hB hbound using hc.exists_bound_iteratedFDeriv hf
  exact ⟨B, hB, fun k x => hbound k k le_rfl x⟩

structure Localizers (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) (K : Set (X F ζ hζ U)) where
  count : ℕ
  chart : Fin count → Chart F ζ hζ hF U A

  ellipticity : Fin count → ℝ
  positive_ellipticity : ∀ i, 0 < ellipticity i
  uniform_ellipticity : ∀ i x, x ∈ closure (Metric.ball (0 : E (chart i).n) (chart i).radius) →
    ∀ ξ : E (chart i).n,
      ellipticity i * ‖ξ‖ ^ 2 ≤
        ∑ j, ∑ k, (chart i).energyMatrix F ζ hζ hF U x j k * ξ j * ξ k
  phi : Fin count → X F ζ hζ U → ℝ
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ hF U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun z => phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (X F ζ hζ U)
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

 variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

def ofRawRealization
    (M : CoreChartLocalizers.Realization F ζ hζ hF U A) :
    Realization F ζ hζ hF U A :=
  {
    representative := M.representative
     }

 def ofRawChart
    (C : CoreChartLocalizers.Chart F ζ hζ hF U A) :
    Chart F ζ hζ hF U A :=
  { n := C.n
    positive_n := C.positive_n
    a := C.a
    positive_a := C.positive_a
    radius := C.radius
    positive_radius := C.positive_radius
    closed_ball_in_cube := C.closed_ball_in_cube
    component := C.component
    center := C.center
    finite_stabilizer := C.finite_stabilizer
    orthogonal := C.orthogonal
    extendedDomain := C.extendedDomain
    open_extendedDomain := C.open_extendedDomain
    closed_ball_in_extension := C.closed_ball_in_extension
    invariant_extension := C.invariant_extension
    coordinates := C.coordinates
    smooth_coordinates := C.smooth_coordinates
    coordinates_embedding := C.coordinates_embedding
    coordinates_open := C.coordinates_open
    smooth_inverse := C.smooth_inverse
    equivariance := C.equivariance
    separated := C.separated
    weight := C.weight
    smooth_weight := C.smooth_weight
    lower := C.lower
    upper := C.upper
    positive_lower := C.positive_lower
    finite_bounds := C.finite_bounds
    coordinate_volume := C.coordinate_volume }

 def ofRawLocalizers
    (M : CoreChartLocalizers.Realization F ζ hζ hF U A)
    {K : Set (X F ζ hζ U)} (hK : MeasurableSet K)
    (C : CoreChartLocalizers.FiniteCutoffs F ζ hζ hF U A K)
    (P : CoreChartLocalizers.FrameComparison F ζ hζ hF U A M C)
    (B : CoreChartLocalizers.LocalOperators F ζ hζ hF U A M C P) :
    Localizers F ζ hζ hF U A (ofRawRealization F ζ hζ hF U A M) K := by
  refine {
    count := C.count
    chart := fun i => ofRawChart F ζ hζ hF U A (C.chart i)
    ellipticity := C.ellipticity
    positive_ellipticity := C.positive_ellipticity
    uniform_ellipticity := C.uniform_ellipticity
    phi := C.phi
    support_phi := C.support_phi
    smooth_phi := C.smooth_phi
    neighborhood := C.neighborhood
    covers_compact := C.covers_compact
    partition := C.partition
    cutoff := C.cutoff
    cutoff_formula := C.cutoff_formula
    smooth_cutoff := C.smooth_cutoff
    compact_cutoff := C.compact_cutoff
    support_cutoff := C.support_cutoff
    invariant_cutoff := C.invariant_cutoff
     }

theorem actual_realization_and_localizers :
    ∃ M : Realization F ζ hζ hF U A,
      ∀ K : Set (X F ζ hζ U), IsCompact K →
        Nonempty (Localizers F ζ hζ hF U A M K) := by
  obtain ⟨M⟩ := CoreChartLocalizers.measurable_realization F ζ hζ hF U A
  refine ⟨ofRawRealization F ζ hζ hF U A M, ?_⟩
  intro K hK
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  letI : T2Space (X F ζ hζ U) :=
    CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U A
  obtain ⟨C⟩ := CoreChartLocalizers.finite_cutoffs F ζ hζ hF U A K hK
  obtain ⟨P⟩ := CoreChartLocalizers.frame_comparison F ζ hζ hF U A M C
  obtain ⟨B⟩ := CoreChartLocalizers.bounded_local_operators F ζ hζ hF U A M
    hK.measurableSet C P
  exact ⟨ofRawLocalizers F ζ hζ hF U A M hK.measurableSet C P B⟩

end KPCoreChartLocalizers

end DedekindZetaZeroFree

end
