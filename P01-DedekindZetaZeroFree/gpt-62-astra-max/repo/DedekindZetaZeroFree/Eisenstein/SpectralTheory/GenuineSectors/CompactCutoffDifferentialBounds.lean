module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential

@[expose] public section

noncomputable section
open scoped Classical NumberField
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

private alias continuous_labeledA_self := DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension.continuous_labeledA_placeEquiv
private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self
private theorem continuous_q (a : ActualChart (U := U) (H := H)) : Continuous (q a) := by apply @DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension.ChartZeroExtension.continuous_q <;> assumption

alias CompactCutoffDifferentialBounds.continuous_q := continuous_q
private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by apply @DedekindZetaZeroFree.KPContActualCotangentPieceReconstruction.HilbertPieceReconstruction.q_coordinates' <;> assumption
 def zext (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem smooth_zext {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (zext a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  refine hg.congr ?_
  intro x hx
  simpa [zext, hx] using (he ⟨x, hx⟩).symm

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (zext a f) x.val)) := by apply @DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.smooth_differential <;> assumption

private alias differential_frame := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.differential_frame

alias CompactCutoffDifferentialBounds.differential_frame := differential_frame

private alias differential_frame_sum := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.differential_frame_sum

alias CompactCutoffDifferentialBounds.differential_frame_sum := differential_frame_sum

private alias differential_arrow_const := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.differential_arrow_const

alias CompactCutoffDifferentialBounds.differential_arrow_const := differential_arrow_const

private alias smooth_ofReal := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.smooth_ofReal

alias CompactCutoffDifferentialBounds.smooth_ofReal := smooth_ofReal

private theorem differentiable_zext {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (zext a f) x.val :=
  ((smooth_zext hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private alias la := DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.RationalOverlapBranches.la

alias CompactCutoffDifferentialBounds.la := la
private alias al := DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.RationalOverlapBranches.al

alias CompactCutoffDifferentialBounds.al := al
 def coord (g : KPCuspArithmetic.PGL2 F) (x : M F) :=
  labeledAInv (placeEquiv F ζ hζ) (g • labeledA (placeEquiv F ζ hζ) x)
local notation "cmap" => coord (ζ:=ζ) (hζ:=hζ)

 theorem coord_continuous (g : KPCuspArithmetic.PGL2 F) : Continuous (coord (ζ:=ζ) (hζ:=hζ) g) := by apply @DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.coord_continuous <;> assumption
 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g = cmap g.val := by apply @DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.chart_coord <;> assumption
 alias chart_omega := DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.chart_omega
 theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) := by apply @isOpen_omega <;> assumption
 alias omega_subset := DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.omega_subset
 section

variable (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))

def make :
    ActualBranch a b := by
  let he := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  have ht : Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
      (omega a ∩ cmap g.val ⁻¹' omega b) (isotropyChart b).omega := by
    rw [chart_coord a b h g]
    exact fun _ hx => omega_subset b hx.2
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := he.choose⁻¹, levelLift := he.choose_spec.choose,
      finite_comparison := by simpa using he.choose_spec.choose_spec
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
include h in
private theorem q_coord
    (x : M F) : q b (cmap g.val x) = q a x := by apply @DedekindZetaZeroFree.KPContCotangentOverlapRationalBranches.RationalOverlapBranches.q_coord <;> assumption

end

private theorem q_branch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) : q b (e.arrow.psi x) = q a x := by apply @DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension.q_actualBranch <;> assumption

section

variable (η : RealSmoothCutoff F ζ hζ U R P H)

private theorem cutoff_norm_branch
    {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) (hx : x ∈ e.arrow.domain) :
    ‖cutoffDifferential η b ⟨e.arrow.psi x, e.target_shrinking hx⟩‖ =
      ‖cutoffDifferential η a ⟨x, e.source_shrinking hx⟩‖ := by
  have hu (a : ActualChart) : SmoothOnLift a (cutoffLift η a) :=
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

private theorem cutoff_norm_fiber
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
  let a : ActualChart := ⟨i,ca,oa,da,dao,dac,das,dai⟩
  let b : ActualChart := ⟨i,cb,ob,db,dbo,dbc,dbs,dbi⟩
  have he : cmap g.val⁻¹ x.val = y.val := by
    rw [coord, ← hg, inv_smul_smul, al]
  refine ⟨make a b rfl g⁻¹, ⟨x.property, ?_⟩, ?_⟩
  · change cmap (g⁻¹).val x.val ∈ omega b
    simpa only [Subgroup.coe_inv, he] using y.property
  · change coordinateMap (isotropyChart a) (targetChart a b rfl) g⁻¹ x.val = y.val
    rw [chart_coord, Subgroup.coe_inv, he]

private theorem cutoff_norm_continuous
    (a : ActualChart (U := U) (H := H)) : Continuous (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) := by
  obtain ⟨g,hg,he⟩ := smooth_differential (smooth_ofReal (η.smooth a))
  have h : (fun x : omega a => cutoffDifferential η a x) = (omega a).domRestrict g := by
    funext x; exact (he x).symm
  rw [show (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) =
    (fun x : omega a => ‖g x.val‖ ^ 2) from congrArg (fun f => fun x => ‖f x‖ ^ 2) h]
  exact hg.continuousOn.restrict.norm.pow 2

end

private theorem exists_chart_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by apply @DedekindZetaZeroFree.KPContActualCotangentMeasurableFamilies.MeasurableFamilies.exists_lift <;> assumption

private theorem continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs

alias CompactCutoffDifferentialBounds.continuous_iff_isQuotientMap := continuous_iff_isQuotientMap
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

alias CompactCutoffDifferentialBounds.continuous_of_all_lifts := continuous_of_all_lifts
private theorem cutoff_continuous (η : RealSmoothCutoff F ζ hζ U R P H) : Continuous η.val := by
  apply continuous_of_all_lifts
  intro a
  obtain ⟨g,hg,he⟩ := η.smooth a
  convert hg.continuousOn.domRestrict using 1
  exact funext (fun y => (he y).symm)

alias CompactCutoffDifferentialBounds.cutoff_continuous := cutoff_continuous
section

variable (η : RealSmoothCutoff F ζ hζ U R P H)

private theorem cutoffDifferential_zero
    (a : ActualChart (U := U) (H := H)) (y : omega a)
    (hy : q a y.val ∉ tsupport η.val) : cutoffDifferential η a y = 0 := by
  have hz : η.val =ᶠ[𝓝 (q a y.val)] 0 := by
    filter_upwards [(isClosed_tsupport η.val).isOpen_compl.mem_nhds hy] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hcomp := hz.comp_tendsto (continuous_q a).continuousAt
  have hext : liftExtension a (cutoffLift η a) =ᶠ[𝓝 y.val] 0 := by
    filter_upwards [hcomp, (isOpen_omega a).mem_nhds y.property] with x hx hmem
    have hh : η.val (q a x) = 0 := hx
    simp only [liftExtension, dite_eq_left hmem, cutoffLift, hh, Complex.ofReal_zero, Pi.zero_apply]
  ext ⟨i,k⟩
  fin_cases k <;> simp [cutoffDifferential, chartDifferential, CotangentLogCoframe.j,
    HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hext.fderiv_eq]

private theorem cutoffNorm_descends :
    ∃ f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ, Continuous f ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a),
        f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
  choose chart point hpoint using (exists_chart_point (R := R) (P := P) (H := H))
  let f := fun x => ‖cutoffDifferential η (chart x) (point x)‖ ^ 2
  have hf (a : ActualChart) (y : omega a) :
      f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
    dsimp only [f]
    rw [cutoff_norm_fiber η (chart (q a y.val)) a (point (q a y.val)) y (hpoint _)]
  refine ⟨f, ?_, hf⟩
  apply continuous_of_all_lifts
  intro a
  convert cutoff_norm_continuous η a using 1
  exact funext (hf a)

end

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
          obtain ⟨f,hf,hchart⟩ := cutoffNorm_descends η
          have hsupport : tsupport f ⊆ tsupport η.val := by
            apply closure_minimal ?_ (isClosed_tsupport η.val)
            intro x hx
            by_contra hn
            obtain ⟨a,y,hy⟩ := exists_chart_point x
            refine hx ?_
            rw [← hy, hchart,(cutoffDifferential_zero η a y (hy ▸ hn)),norm_zero,zero_pow (by decide)]
          have hcompactf : HasCompactSupport f :=
            hcompact.of_isClosed_subset (isClosed_tsupport f) hsupport
          obtain ⟨B,hB⟩ := hcompact.isCompact.exists_bound_of_continuousOn (cutoff_continuous η).continuousOn
          obtain ⟨D,hD⟩ := hcompactf.isCompact.exists_bound_of_continuousOn hf.continuousOn
          refine ⟨max B 0, Real.sqrt (max D 0), le_max_right _ _, Real.sqrt_nonneg _, ?_, ?_⟩
          · intro x
            by_cases hx : x ∈ tsupport η.val
            · have hh : |η.val x| ≤ B := by simpa using hB x hx
              exact hh.trans (le_max_left _ _)
            · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero]
              exact le_max_right _ _
          · intro a y
            have hs : f (q a y.val) ≤ max D 0 := by
              by_cases hx : q a y.val ∈ tsupport f
              · have hh : |f (q a y.val)| ≤ D := by simpa using hD _ hx
                exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
              · rw [image_eq_zero_of_notMem_tsupport hx]; exact le_max_right _ _
            rw [hchart] at hs
            exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hs

end DedekindZetaZeroFree.KPContActualSectorMultiplier

end
