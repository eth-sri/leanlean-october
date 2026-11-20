module
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.HeightExhaustion

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspCutoffBoundaryVanishing
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.HausdorffTopology

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.GenericZeroExtension
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
    (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
 abbrev S := KPFiniteCuspAtlas.SymmetricSpace F
 abbrev I := Σ i : Fin a.componentCount, Fin (a.cuspAtlas i).cuspCount
 def Q (i : Fin a.componentCount) (x : S (F := F)) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) (KPCuspSiegel.projection F _ x)
 def L (c : I a) (z : KPCuspCharts.Coordinates F) :=
  Q a c.1 (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z)
 section

variable (τ : ℝ) (c : I a)

def E :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative c.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
      ((a.cuspAtlas c.1).representative c.2) τ
 def t (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) : ℝ :=
  if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a c z = x
  then (Classical.choose h).2 else 0
 def zeroExtension (φ : ℝ → ℝ) :=
  (E a τ c).indicator (fun x => φ (t a τ c x))

end
private theorem Q_cont (i : Fin a.componentCount) : Continuous (Q a i) :=
  continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)

alias CompactHeightSublevels.Q_cont := Q_cont
section

variable (i : Fin a.componentCount)

private theorem Q_invariant
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) (x : S (F := F)) :
    Q a i (g.val • x) = Q a i x := by
  unfold Q
  congr 1
  exact KPCuspSiegel.projection_action F _ g x
private theorem component_injective :
    Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)) := by apply @DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.ExhaustionGeometry.component_injective <;> assumption
private theorem same_component (c : I a)
    (x : S (F := F)) (z : KPCuspCharts.Coordinates F)
    (he : Q a i x = L a c z) : i = c.1 := by
  have hh : a.components ⟨i, KPCuspSiegel.projection F _ x⟩ =
      a.components ⟨c.1, KPCuspSiegel.projection F _
        (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z)⟩ := by
    simpa only [a.components_formula, Q, L] using he
  exact congrArg Sigma.fst (a.components.injective hh)

end
 def localHeight (γ : KPCuspArithmetic.PGL2 F) (x : S (F := F)) : ℝ :=
  KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (γ • x)
private theorem localHeight_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (localHeight γ) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)) := by
    unfold KPCuspLogShape.meanHeight
    fun_prop
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun x : S (F := F) => γ • x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (KPCuspSiegel.action F γ)
    unfold KPCuspSiegel.action KPCuspSiegel.glAction
    exact (KPArch.productAction_contDiff _ _).of_le (by simp)
  exact ht.comp ha

alias CompactHeightSublevels.localHeight_smooth := localHeight_smooth
private theorem local_lift (c : I a) (hd : 0 < KPCuspLogShape.dimension F)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
    (y : S (F := F)) :
    L a c ((KPCuspCharts.toArchHomeomorph F hd).symm
      ((((a.cuspAtlas c.1).representative c.2)⁻¹) • g.val⁻¹ • y)) = Q a c.1 y := by
  change Q a c.1 (((a.cuspAtlas c.1).representative c.2) •
    (KPCuspCharts.toArchHomeomorph F hd) ((KPCuspCharts.toArchHomeomorph F hd).symm _)) = _
  rw [Homeomorph.apply_symm_apply, smul_inv_smul]
  simpa using Q_invariant a c.1 g⁻¹ y
private theorem end_open (τ : ℝ) (c : I a) : IsOpen (E a τ c) := by
  have hc : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative c.1)) := by
    simpa only [Function.comp_def, a.components_formula] using (a.components.isOpenMap.comp (isOpenMap_sigmaMk))
  exact hc _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ τ)
section

variable (τ : ℝ) (hτ : a.threshold ≤ τ) (c : I a)

include hτ in
private theorem lift_range :
    L a c '' {z : KPCuspCharts.Coordinates F | τ < z.2} = E a τ c := (KPActualCollarBuffer.actual_height_descent F ζ hζ hF U a τ hτ).1 c
include hτ in
private theorem height_coordinates (z : KPCuspCharts.Coordinates F) (hz : τ < z.2) : t a τ c (L a c z) = z.2 := (KPActualCollarBuffer.actual_height_descent F ζ hζ hF U a τ hτ).2.1 c z hz

end
private theorem interior_height (τ : ℝ) (hτ : a.threshold ≤ τ) (c : I a)
    (x : S (F := F)) (hx : Q a c.1 x ∈ E a τ c) :
    ∃ γ : KPCuspArithmetic.PGL2 F, (fun y => t a τ c (Q a c.1 y)) =ᶠ[𝓝 x] localHeight γ := by
  rw [← lift_range a τ hτ c] at hx
  obtain ⟨z,hz,he⟩ := hx
  have he' : KPCuspSiegel.projection F _
      (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z) =
      KPCuspSiegel.projection F _ x := component_injective a c.1 he
  obtain ⟨g,hg⟩ := Quotient.exact he'.symm
  change g.val • (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z) = x at hg
  let γ := ((a.cuspAtlas c.1).representative c.2)⁻¹ * g.val⁻¹
  have hd := KPCuspCharts.positive_dimension F hF
  have ht : localHeight γ x = z.2 := by
    dsimp [localHeight, γ]
    rw [mul_smul, ← hg, inv_smul_smul, inv_smul_smul]
    exact KPCuspCharts.toArch_meanHeight F hd z
  refine ⟨γ, ?_⟩
  have hopen : IsOpen {y : S (F := F) | τ < localHeight γ y} :=
    isOpen_lt continuous_const (localHeight_smooth γ).continuous
  have htx : x ∈ {y : S (F := F) | τ < localHeight γ y} := by
    change τ < localHeight γ x
    rw [ht]; exact hz
  filter_upwards [hopen.mem_nhds htx] with y hy
  let w := (KPCuspCharts.toArchHomeomorph F hd).symm (γ • y)
  have hw : w.2 = localHeight γ y := rfl
  have hl : L a c w = Q a c.1 y := by
    dsimp only [w, γ]
    rw [mul_smul]
    exact local_lift a c hd g y
  rw [← hl, height_coordinates a τ hτ c w (hw ▸ hy), hw]
section

variable (τ T : ℝ) (hτ : a.threshold ≤ τ) (hT : τ < T) (c : I a) (φ : ℝ → ℝ)

include hτ hT in
private theorem zero_germ (hzero : ∀ u, u ≤ T → φ u = 0)
    (p : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hp : p ∉ E a τ c) :
    zeroExtension a τ c φ =ᶠ[𝓝 p] 0 := by
  by_cases hc : p ∈ closure (E a τ c)
  · have hf : p ∈ frontier (E a τ c) := by
      rw [frontier, (end_open a τ c).interior_eq]
      exact ⟨hc,hp⟩
    obtain ⟨V,hV,hpV,hbound⟩ :=
      (KPActualCollarBuffer.actual_boundary_zero_buffer F ζ hζ hF U a τ T hτ hT).1 c p hf
    filter_upwards [hV.mem_nhds hpV] with y hy
    by_cases he : y ∈ E a τ c
    · simp only [zeroExtension, Set.indicator_of_mem he, Pi.zero_apply]
      exact hzero _ (le_of_lt (hbound y hy he))
    · simp [zeroExtension, he]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have he : y ∉ E a τ c := fun he => hy (subset_closure he)
    simp [zeroExtension, he]
include hτ hT in
private theorem zeroExtension_smooth (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : ∀ u, u ≤ T → φ u = 0) (i : Fin a.componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : S (F := F) => zeroExtension a τ c φ (Q a i x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Q a i x ∈ E a τ c
  · have hi : i = c.1 := by
      have hh := hx
      rw [← lift_range a τ hτ c] at hh
      obtain ⟨z,hz,he⟩ := hh
      exact same_component a i c x z he.symm
    subst i
    obtain ⟨γ, he⟩ := interior_height a τ hτ c x hx
    have hf : (fun y : S (F := F) => zeroExtension a τ c φ (Q a c.1 y)) =ᶠ[𝓝 x]
        (fun y => φ (localHeight γ y)) := by
      filter_upwards [he, ((end_open a τ c).preimage (Q_cont a c.1)).mem_nhds hx] with y hy hmem
      change Q a c.1 y ∈ E a τ c at hmem
      simp only [zeroExtension, Set.indicator_of_mem hmem, hy]
    exact ((hφ.comp (localHeight_smooth γ)).contDiffAt).congr_of_eventuallyEq hf
  · have he := (zero_germ a τ T hτ hT c φ hzero (Q a i x) hx).comp_tendsto
      (Q_cont a i).continuousAt
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he
include hτ hT in
private theorem zeroExtension_continuous (hφ : Continuous φ) (hzero : ∀ u, u ≤ T → φ u = 0) :
    Continuous (zeroExtension a τ c φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ E a τ c
  · have he : zeroExtension a τ c φ =ᶠ[𝓝 x] (fun y => φ (t a τ c y)) := by
      filter_upwards [(end_open a τ c).mem_nhds hx] with y hy
      exact Set.indicator_of_mem hy _
    exact (hφ.continuousAt.comp ((((KPActualCollarBuffer.actual_height_descent F ζ hζ hF U a τ hτ).2.2.1 c) x hx).continuousAt ((end_open a τ c).mem_nhds hx))).congr he.symm
  · exact continuousAt_const.congr (zero_germ a τ T hτ hT c φ hzero x hx).symm

end

theorem scalar_zeroExtension_smooth_continuous
    (τ T : ℝ) (hτ : a.threshold ≤ τ) (hT : τ < T)
    (c : Σ i : Fin a.componentCount, Fin (a.cuspAtlas i).cuspCount)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : ∀ u, u ≤ T → φ u = 0) :
    let lift := fun z : KPCuspCharts.Coordinates F =>
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (((a.cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z),
          a.representative c.1)
    let endRegion := KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative c.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
        ((a.cuspAtlas c.1).representative c.2) τ
    let height := fun x : KPFiniteCuspAtlas.rawXU F ζ hζ U =>
      if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ lift z = x
      then (Classical.choose h).2 else 0
    let η := endRegion.indicator (fun x => φ (height x))
    (∀ i : Fin a.componentCount, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : KPFiniteCuspAtlas.SymmetricSpace F => η
        (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
          (KPCuspSiegel.projection F _ x)))) := by
  exact zeroExtension_smooth a τ T hτ hT c φ hφ hzero

theorem scalar_zeroExtension_local_model
    (τ T : ℝ) (hτ : a.threshold ≤ τ) (hT : τ < T)
    (c : Σ i : Fin a.componentCount, Fin (a.cuspAtlas i).cuspCount)
    (φ : ℝ → ℝ) (hzero : ∀ u, u ≤ T → φ u = 0) :
    let lift := fun z : KPCuspCharts.Coordinates F =>
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (((a.cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z),
          a.representative c.1)
    let endRegion := KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative c.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
        ((a.cuspAtlas c.1).representative c.2) τ
    let height := fun x : KPFiniteCuspAtlas.rawXU F ζ hζ U =>
      if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ lift z = x
      then (Classical.choose h).2 else 0
    let η := endRegion.indicator (fun x => φ (height x))
    ∀ (i : Fin a.componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F),
      (fun y => η (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
        (KPCuspSiegel.projection F _ y))) =ᶠ[𝓝 x] 0 ∨
      ∃ γ : KPCuspArithmetic.PGL2 F,
        (fun y => η (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
          (KPCuspSiegel.projection F _ y))) =ᶠ[𝓝 x]
        (fun y => φ (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (γ • y))) := by
  change ∀ i x, (fun y => zeroExtension a τ c φ (Q a i y)) =ᶠ[𝓝 x] 0 ∨
    ∃ γ : KPCuspArithmetic.PGL2 F,
      (fun y => zeroExtension a τ c φ (Q a i y)) =ᶠ[𝓝 x]
        (fun y => φ (localHeight γ y))
  intro i x
  by_cases hx : Q a i x ∈ E a τ c
  · have hi : i = c.1 := by
      rw [← lift_range a τ hτ c] at hx
      obtain ⟨z,hz,he⟩ := hx
      exact same_component a i c x z he.symm
    subst i
    obtain ⟨γ, he⟩ := interior_height a τ hτ c x hx
    refine Or.inr ⟨γ, ?_⟩
    filter_upwards [he, ((end_open a τ c).preimage (Q_cont a c.1)).mem_nhds hx]
      with y hy hmem
    change Q a c.1 y ∈ E a τ c at hmem
    simp only [zeroExtension, Set.indicator_of_mem hmem, hy]
  · exact Or.inl ((zero_germ a τ T hτ hT c φ hzero (Q a i x) hx).comp_tendsto
      (Q_cont a i).continuousAt)

 section

variable (c : I a)

abbrev stabilizer := KPCuspArithmetic.conjugatedStabilizer F
  (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
  ((a.cuspAtlas c.1).cusp c.2) ((a.cuspAtlas c.1).representative c.2)
 def totalEndMap : KPCuspCharts.TotalQuotient F (stabilizer a c) →
    KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  Quotient.lift (L a c) (by
    intro z w h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    unfold L Q
    congr 1
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨KPCuspGenuineMonodromy.cuspInclusion F _ _ _ g, ?_⟩
    change (KPCuspGenuineMonodromy.cuspInclusion F _ _ _ g : KPCuspArithmetic.PGL2 F) •
      (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F w) =
      ((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (fun x => ((a.cuspAtlas c.1).representative c.2) • x) hg)
private theorem totalEndMap_continuous : Continuous (totalEndMap a c) := by
  apply continuous_quot_lift
  exact (Q_cont a c.1).comp
    ((KPCuspSiegel.continuous_action F _).comp (KPCuspCharts.toArchHomeomorph F ((a.cuspAtlas c.1).geometry c.2).positive_dimension).continuous)

end
 variable (T : ℝ)

def boundedStrip (c : I a) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  (totalEndMap a c ∘ ((a.cuspAtlas c.1).geometry c.2).radialPresentation) ''
    (Set.univ ×ˢ Set.Icc a.threshold T)
private theorem boundedStrip_compact (c : I a) : IsCompact (boundedStrip a T c) := by
  letI := ((a.cuspAtlas c.1).geometry c.2).compact_cross
  exact (isCompact_univ.prod isCompact_Icc).image
    ((totalEndMap_continuous a c).comp ((a.cuspAtlas c.1).geometry c.2).radialPresentation.continuous)
private theorem compact_sublevel :
    IsCompact ((⋃ c : I a, E a T c)ᶜ) := by
  letI := CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U a
  have hcore : IsCompact ((⋃ c : I a, E a a.threshold c)ᶜ) := by
    simpa only [Set.iUnion_sigma, E, Set.compl_eq_univ_sdiff] using a.compact_core
  apply (hcore.union
    (isCompact_iUnion (boundedStrip_compact a T))).of_isClosed_subset
  · exact (isOpen_iUnion (end_open a T)).isClosed_compl
  · intro x hx
    by_cases he : x ∈ ⋃ c : I a, E a a.threshold c
    · right
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp he
      rw [← lift_range a a.threshold le_rfl c] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      have hzT : z.2 ≤ T := by
        by_contra hn
        apply hx
        apply Set.mem_iUnion.mpr
        refine ⟨c, ?_⟩

        exact ⟨KPCuspSiegel.projection F _
          (((a.cuspAtlas c.1).representative c.2) • KPCuspCharts.toArch F z),
          ⟨_, ⟨_, by
            change T < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F z)
            rw [KPCuspCharts.toArch_meanHeight F (KPCuspCharts.positive_dimension F hF)]
            exact lt_of_not_ge hn, rfl⟩, rfl⟩, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨c, ?_⟩
      refine ⟨(Quotient.mk _ z.1, z.2), ⟨Set.mem_univ _, hz.le, hzT⟩, ?_⟩
      change totalEndMap a c (((a.cuspAtlas c.1).geometry c.2).radialPresentation
        (Quotient.mk _ z.1, z.2)) = L a c z
      rw [((a.cuspAtlas c.1).geometry c.2).radialPresentation_formula]
      rfl
    · exact Or.inl he

theorem height_sublevel_isCompact :
    IsCompact ((Set.univ : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) \
      (⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
        KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
          KPFiniteCuspAtlas.endSet F
            (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
            ((a.cuspAtlas i).representative c) T)) := by
  simpa only [Set.iUnion_sigma, E, Set.compl_eq_univ_sdiff] using compact_sublevel a T
end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.GenericZeroExtension

end
