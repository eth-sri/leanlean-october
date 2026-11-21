module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorMultiplier

open KPContActualSectorTestDifferentialDescentCalculus (smooth_differential differential_arrow_const smooth_ofReal differentiable_zext)
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentPieceHilbertSum
open KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem isOpen_chart_lift (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  KPContActualSectorTestDifferentialDescentCalculus.isOpen_omega a

theorem continuous_chart_projection (a : ActualChart (U := U) (H := H)) : Continuous (q a) :=
  KPContActualSectorTestDifferentialDescentCalculus.continuous_q a

 def zext (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem la (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) = x := by
  funext k
  simp [labeledA, labeledAInv]
private theorem al (x : M F) :
    labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) x) = x := by
  simp [labeledA, labeledAInv]
 def coord (g : KPCuspArithmetic.PGL2 F) (x : M F) :=
  labeledAInv (placeEquiv F ζ hζ) (g • labeledA (placeEquiv F ζ hζ) x)
local notation "cmap" => coord (ζ:=ζ) (hζ:=hζ)

 theorem coord_continuous (g : KPCuspArithmetic.PGL2 F) : Continuous (coord (ζ:=ζ) (hζ:=hζ) g) := by
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp ((KPCuspSiegel.continuous_action F g).comp (by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous))
 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g = cmap g.val := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [coordinateMap, isotropyChart, targetChart, ChartKind.representative, coord]
 theorem chart_omega (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).omega = (isotropyChart b).omega := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  rfl
 theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) := by
  apply a.domain_open.preimage
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
 theorem omega_subset (a : ShrunkChart F ζ hζ U R P H) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)
 def make (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    ActualBranch a b := by
  let he := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  let r := he.choose
  let u := he.choose_spec.choose
  have hu := he.choose_spec.choose_spec
  have ht : Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
      (omega a ∩ cmap g.val ⁻¹' omega b) (isotropyChart b).omega := by
    rw [chart_coord a b h g]
    exact fun _ hx => omega_subset b hx.2
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := r⁻¹, levelLift := u,
      finite_comparison := by simpa only [inv_inv] using hu
      domain := omega a ∩ cmap g.val ⁻¹' omega b
      isOpen_domain := (omega_open a).inter ((omega_open b).preimage (coord_continuous g.val))
      source := fun _ hx => omega_subset a hx.1
      target := by rw [chart_omega a b h]; exact ht }
    source_shrinking := fun _ hx => hx.1
    target_shrinking := by
      change Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
        (omega a ∩ cmap g.val ⁻¹' omega b) (omega b)
      rw [chart_coord a b h g]
      exact fun _ hx => hx.2
    target_larger := ht }
private theorem q_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))
    (x : M F) : q b (cmap g.val x) = q a x := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  simp only [coord, la]
  apply Quotient.sound
  exact ⟨g, rfl⟩

private theorem q_branch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) : q b (e.arrow.psi x) = q a x := by
  rw [show e.arrow.psi = cmap e.arrow.gamma.val from chart_coord a b e.component_eq e.arrow.gamma]
  exact q_coord a b e.component_eq e.arrow.gamma x

private theorem cutoff_norm_branch (η : RealSmoothCutoff F ζ hζ U R P H)
    {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) (hx : x ∈ e.arrow.domain) :
    ‖cutoffDifferential η b ⟨e.arrow.psi x, e.target_shrinking hx⟩‖ =
      ‖cutoffDifferential η a ⟨x, e.source_shrinking hx⟩‖ := by
  have hu (a : ActualChart (U := U) (H := H)) : SmoothOnLift a (cutoffLift η a) :=
    smooth_ofReal (η.smooth a)
  have he : (fun y => zext b (cutoffLift η b) (e.arrow.psi y)) =ᶠ[𝓝 x]
      (1:ℂ) • zext a (cutoffLift η a) := by
    filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
    simp [zext, e.source_shrinking hy, e.target_shrinking hy,
      cutoffLift, q_branch e y]
  have hd := differential_arrow_const e.arrow 1
    (zext a (cutoffLift η a)) (zext b (cutoffLift η b)) x hx
    (differentiable_zext (hu a) ⟨x,e.source_shrinking hx⟩)
    (differentiable_zext (hu b) ⟨_,e.target_shrinking hx⟩) he
  rw [one_smul] at hd
  change ‖CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (zext b (cutoffLift η b)) (e.arrow.psi x))‖ = _
  rw [hd]
  exact (KPContCotangentRealOrthogonalComplexification.orthogonalComplexification _
    (KPContCotangentActualGenuineTwistIsotropy.q e.arrow x hx)).norm_map _

private theorem cutoff_norm_fiber (η : RealSmoothCutoff F ζ hζ U R P H)
    (a b : ActualChart (U := U) (H := H)) (x : omega a) (y : omega b)
    (hxy : q a x.val = q b y.val) :
    ‖cutoffDifferential η a x‖ = ‖cutoffDifferential η b y‖ := by
  have hc : a.component = b.component := by
    have he : (H.atlas U).components
        ⟨a.component, KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ) x.val)⟩ =
      (H.atlas U).components
        ⟨b.component, KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ) y.val)⟩ := by
      simpa only [(H.atlas U).components_formula, KPContCotangentOverlapRationalBranches.q] using hxy
    exact congrArg Sigma.fst ((H.atlas U).components.injective he)
  suffices he : ∃ (e : ActualBranch a b) (hx : x.val ∈ e.arrow.domain), e.arrow.psi x.val = y.val by
    obtain ⟨e,hx,he⟩ := he
    simpa [he] using (cutoff_norm_branch η e x.val hx).symm
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at hc
  subst j
  have hi : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative i)) := by
    intro u v huv
    have he : (H.atlas U).components ⟨i,u⟩ = (H.atlas U).components ⟨i,v⟩ := by
      simpa only [(H.atlas U).components_formula] using huv
    exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
  obtain ⟨g,hg⟩ := Quotient.exact (hi hxy)
  change g.val • labeledA (placeEquiv F ζ hζ) y.val = labeledA (placeEquiv F ζ hζ) x.val at hg
  let a : ActualChart (U := U) (H := H) := ⟨i,ca,oa,da,dao,dac,das,dai⟩
  let b : ActualChart (U := U) (H := H) := ⟨i,cb,ob,db,dbo,dbc,dbs,dbi⟩
  have he : cmap g.val⁻¹ x.val = y.val := by
    rw [coord, ← hg, inv_smul_smul, al]
  refine ⟨make a b rfl g⁻¹, ⟨x.property, ?_⟩, ?_⟩
  · change cmap (g⁻¹).val x.val ∈ omega b
    simpa only [Subgroup.coe_inv, he] using y.property
  · change coordinateMap (isotropyChart a) (targetChart a b rfl) g⁻¹ x.val = y.val
    rw [chart_coord, Subgroup.coe_inv, he]

private theorem cutoff_norm_continuous (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) : Continuous (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) := by
  obtain ⟨g,hg,he⟩ := smooth_differential (smooth_ofReal (η.smooth a))
  have h : (fun x : omega a => cutoffDifferential η a x) = (omega a).domRestrict g := by
    funext x; exact (he x).symm
  rw [show (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) =
    (fun x : omega a => ‖g x.val‖ ^ 2) from congrArg (fun f => fun x => ‖f x‖ ^ 2) h]
  exact hg.continuousOn.restrict.norm.pow 2

private theorem cutoffDifferential_zero (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a)
    (hy : q a y.val ∉ tsupport η.val) : cutoffDifferential η a y = 0 := by
  have hz : η.val =ᶠ[𝓝 (q a y.val)] 0 := by
    filter_upwards [(isClosed_tsupport η.val).isOpen_compl.mem_nhds hy] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hcomp := hz.comp_tendsto (continuous_chart_projection a).continuousAt
  have hext : liftExtension a (cutoffLift η a) =ᶠ[𝓝 y.val] 0 := by
    filter_upwards [hcomp, (isOpen_chart_lift a).mem_nhds y.property] with x hx hmem
    have hh : η.val (q a x) = 0 := hx
    simp only [liftExtension, dite_eq_left hmem, cutoffLift, hh, Complex.ofReal_zero, Pi.zero_apply]
  ext ⟨i,k⟩
  fin_cases k <;> simp [cutoffDifferential, chartDifferential, CotangentLogCoframe.j,
    HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hext.fderiv_eq]

theorem cutoffNorm_descends (η : RealSmoothCutoff F ζ hζ U R P H) :
    ∃! f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ, Continuous f ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a),
        f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
  choose chart point hpoint using (exists_chart_lift (R := R) (P := P) (H := H))
  let f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun x => ‖cutoffDifferential η (chart x) (point x)‖ ^ 2
  have hf (a : ActualChart (U := U) (H := H)) (y : omega a) :
      f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
    dsimp only [f]
    rw [cutoff_norm_fiber η (chart (q a y.val)) a (point (q a y.val)) y (hpoint _)]
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · apply continuous_of_chart_lifts
    intro a
    convert cutoff_norm_continuous η a using 1
    exact funext (hf a)
  · intro g hg
    funext x
    obtain ⟨a, y, rfl⟩ := exists_chart_lift (R := R) (P := P) (H := H) x
    rw [hg.2, hf]

private theorem compactBounds (η : RealSmoothCutoff F ζ hζ U R P H) (hcompact : HasCompactSupport η.val) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ (∀ x, |η.val x| ≤ B) ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a), ‖cutoffDifferential η a y‖ ≤ D := by
  obtain ⟨f, ⟨hf, hchart⟩, -⟩ := cutoffNorm_descends η
  have hsupport : tsupport f ⊆ tsupport η.val := by
    apply closure_minimal ?_ (isClosed_tsupport η.val)
    intro x hx
    by_contra hn
    obtain ⟨a,y,hy⟩ := exists_chart_lift (R := R) (P := P) (H := H) x
    have hd := cutoffDifferential_zero η a y (hy ▸ hn)
    have hz : f x = 0 := by rw [← hy, hchart,hd,norm_zero,zero_pow (by decide)]
    exact hx hz
  have hcompactf : HasCompactSupport f :=
    hcompact.of_isClosed_subset (isClosed_tsupport f) hsupport
  obtain ⟨B,hB⟩ := hcompact.isCompact.exists_bound_of_continuousOn η.continuous.continuousOn
  obtain ⟨D,hD⟩ := hcompactf.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0, Real.sqrt (max D 0), le_max_right _ _, Real.sqrt_nonneg _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport η.val
    · have hh : |η.val x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
      exact hh.trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero]
      exact le_max_right _ _
  · intro a y
    have hnonneg : 0 ≤ f (q a y.val) := by rw [hchart]; positivity
    have hs : f (q a y.val) ≤ max D 0 := by
      by_cases hx : q a y.val ∈ tsupport f
      · have hh : |f (q a y.val)| ≤ D := by simpa only [Real.norm_eq_abs] using hD _ hx
        exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
      · rw [image_eq_zero_of_notMem_tsupport hx]; exact le_max_right _ _
    rw [hchart] at hs
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hs

theorem compactCutoff_bounds
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (η : KPContActualSectorTestDifferentialDescent.RealSmoothCutoff F ζ hζ U R P H)
    (hcompact : HasCompactSupport η.val) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ (∀ x, |η.val x| ≤ B) ∧
      ∀ (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
        (y : KPContCotangentOverlapRationalBranches.omega a),
        ‖KPContActualSectorTestDifferentialDescent.cutoffDifferential η a y‖ ≤ D := by
  exact compactBounds η hcompact

end DedekindZetaZeroFree.KPContActualSectorMultiplier

end
