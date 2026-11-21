module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RadialCutoffs.SmoothZeroExtension
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSquareEndPartition

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Base := KPFiniteCuspAtlas.rawXU F ζ hζ U

abbrev CuspIndex := KPContActualCollarBuffer.CuspIndex F ζ hζ U R P H

def AboveEndStarts (T : ℝ) : Prop :=
  ∀ c : CuspIndex F ζ hζ U R P H, ((H.atlas U).cuspAtlas c.1).threshold < T

def differentialSupport (η : Cutoff F ζ hζ U R P H) : Set (Base F ζ hζ U) :=
  closure {x | ∃ (a : ActualChart (U := U) (H := H)) (y : omega a),
    q a y.val = x ∧ cutoffDifferential η a y ≠ 0}

open KPContActualCotangentPieceHilbertSum
open KPContActualSectorMultiplier (cutoffNorm_descends continuous_chart_projection isOpen_chart_lift)

def differentialNormSquared (η : Cutoff F ζ hζ U R P H) : Base F ζ hζ U → ℝ :=
  Classical.choose (cutoffNorm_descends η)

theorem differentialNormSquared_chart (η : Cutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a) :
    differentialNormSquared F ζ hζ U R P H η (q a y.val) =
      ‖cutoffDifferential η a y‖ ^ 2 := by
  exact (Classical.choose_spec (cutoffNorm_descends η)).1.2 a y

theorem differentialSupport_eq_tsupport (η : Cutoff F ζ hζ U R P H) :
    differentialSupport F ζ hζ U R P H η =
      tsupport (differentialNormSquared F ζ hζ U R P H η) := by
  unfold differentialSupport tsupport
  congr 1
  ext x
  constructor
  · rintro ⟨a, y, rfl, hy⟩
    rw [Function.mem_support, differentialNormSquared_chart]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  · intro hx
    obtain ⟨a, y, rfl⟩ := exists_chart_lift (R := R) (P := P) (H := H) x
    rw [Function.mem_support, differentialNormSquared_chart] at hx
    exact ⟨a, y, rfl, fun h => hx (by simp [h])⟩

def collarError (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) : Base F ζ hζ U → ℝ :=
  fun x => differentialNormSquared F ζ hζ U R P H χ₀ x +
    ∑ c, differentialNormSquared F ζ hζ U R P H (χ c) x

theorem continuous_differentialNormSquared (η : Cutoff F ζ hζ U R P H) :
    Continuous (differentialNormSquared F ζ hζ U R P H η) :=
  (Classical.choose_spec (cutoffNorm_descends η)).1.1

theorem differentialNormSquared_nonnegative (η : Cutoff F ζ hζ U R P H) (x : Base F ζ hζ U) :
    0 ≤ differentialNormSquared F ζ hζ U R P H η x := by
  obtain ⟨a, y, rfl⟩ := exists_chart_lift (R := R) (P := P) (H := H) x
  rw [differentialNormSquared_chart]
  exact sq_nonneg _

theorem collarError_continuous_nonnegative (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) :
    Continuous (collarError F ζ hζ U R P H χ₀ χ) ∧
      ∀ x, 0 ≤ collarError F ζ hζ U R P H χ₀ χ x := by
  refine ⟨(continuous_differentialNormSquared F ζ hζ U R P H χ₀).add
    (continuous_finset_sum _ (fun c _ => continuous_differentialNormSquared F ζ hζ U R P H (χ c))), ?_⟩
  intro x
  exact add_nonneg (differentialNormSquared_nonnegative F ζ hζ U R P H χ₀ x)
    (Finset.sum_nonneg (fun c _ => differentialNormSquared_nonnegative F ζ hζ U R P H (χ c) x))

theorem collarError_compact_bounded (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H)
    (h₀ : IsCompact (differentialSupport F ζ hζ U R P H χ₀))
    (hχ : ∀ c, IsCompact (differentialSupport F ζ hζ U R P H (χ c))) :
    HasCompactSupport (collarError F ζ hζ U R P H χ₀ χ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, collarError F ζ hζ U R P H χ₀ χ x ≤ C := by
  have h₀' : HasCompactSupport (differentialNormSquared F ζ hζ U R P H χ₀) := by
    rw [HasCompactSupport, ← differentialSupport_eq_tsupport]; exact h₀
  have hχ' : ∀ c, HasCompactSupport (differentialNormSquared F ζ hζ U R P H (χ c)) := by
    intro c
    rw [HasCompactSupport, ← differentialSupport_eq_tsupport]; exact hχ c
  have hsum : ∀ s : Finset (CuspIndex F ζ hζ U R P H),
      HasCompactSupport (fun x => ∑ c ∈ s, differentialNormSquared F ζ hζ U R P H (χ c) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hχ' a).add ih
  have hc : HasCompactSupport (collarError F ζ hζ U R P H χ₀ χ) :=
    h₀'.add (hsum Finset.univ)
  have hcont := (collarError_continuous_nonnegative F ζ hζ U R P H χ₀ χ).1
  obtain ⟨C, hC⟩ := hcont.bddAbove_range_of_hasCompactSupport hc
  refine ⟨hc, max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)

structure SquareEndPartition (T : ℝ) where
  χ₀ : Cutoff F ζ hζ U R P H
  χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H
  ρ : Cutoff F ζ hζ U R P H
  core_range : ∀ x, 0 ≤ χ₀.val x ∧ χ₀.val x ≤ 1
  cusp_range : ∀ c x, 0 ≤ (χ c).val x ∧ (χ c).val x ≤ 1
  square_sum : ∀ x, χ₀.val x ^ 2 + ∑ c, (χ c).val x ^ 2 = 1
  cusp_support_in_tail : ∀ c, tsupport (χ c).val ⊆
    KPContActualCollarBuffer.endSet F ζ hζ U R P H T c

  error_nonnegative : ∀ x, 0 ≤ collarError F ζ hζ U R P H χ₀ χ x
  error_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, collarError F ζ hζ U R P H χ₀ χ x ≤ C
  rho_range : ∀ x, 0 ≤ ρ.val x ∧ ρ.val x ≤ 1
  compact_rho_support : HasCompactSupport ρ.val

  rho_one_neighborhood : ∃ V : Set (Base F ζ hζ U), IsOpen V ∧
    tsupport χ₀.val ∪ tsupport (collarError F ζ hζ U R P H χ₀ χ) ⊆ V ∧
    ∀ x ∈ V, ρ.val x = 1
  core_multiplier : SectorMultiplier F ζ hζ U R P H χ₀
  cusp_multiplier : ∀ c, SectorMultiplier F ζ hζ U R P H (χ c)
  rho_multiplier : SectorMultiplier F ζ hζ U R P H ρ

section ConstructionHelpers

 def angle (A B t : ℝ) := (Real.pi / 2) * Real.smoothTransition ((t-A)/(B-A))
private theorem angle_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (angle A B) := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))
private theorem angle_zero {A B t : ℝ} (hAB : A < B) (ht : t ≤ A) : angle A B t = 0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (le_of_lt (sub_pos.mpr hAB))), mul_zero]
private theorem angle_one {A B t : ℝ} (hAB : A < B) (ht : B ≤ t) : angle A B t = Real.pi / 2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hAB)).mpr (by linarith)), mul_one]
private theorem angle_range (A B t : ℝ) : 0 ≤ angle A B t ∧ angle A B t ≤ Real.pi / 2 := by
  have hp := le_of_lt Real.pi_pos
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one _)
private theorem sin_range (A B t : ℝ) : 0 ≤ Real.sin (angle A B t) ∧ Real.sin (angle A B t) ≤ 1 := by
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (angle_range A B t).1 (by have := (angle_range A B t).2; have := Real.pi_pos; linarith), Real.sin_le_one _⟩
private theorem cos_range (A B t : ℝ) : 0 ≤ Real.cos (angle A B t) ∧ Real.cos (angle A B t) ≤ 1 := by
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by have := (angle_range A B t).1; have := Real.pi_pos; linarith, (angle_range A B t).2⟩, Real.cos_le_one _⟩

 def sumCutoff {ι : Type*} (s : Finset ι) (η : ι → Cutoff F ζ hζ U R P H) : Cutoff F ζ hζ U R P H :=
  ⟨fun x => ∑ i ∈ s, (η i).val x, fun a => by
    choose g hg he using (fun i => (η i).smooth a)
    refine ⟨fun x => ∑ i ∈ s, g i x, ?_, ?_⟩
    · exact ContDiffOn.sum (fun i _ => hg i)
    · intro x; simp only [he]⟩
private theorem differential_zero_of_germ (η : Cutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) (r : ℝ)
    (he : (fun y => η.val (q a y)) =ᶠ[𝓝 x.val] (fun _ => r)) :
    cutoffDifferential η a x = 0 := by
  have hext : liftExtension a (cutoffLift η a) =ᶠ[𝓝 x.val] (fun _ => (r : ℂ)) := by
    filter_upwards [he, (isOpen_chart_lift a).mem_nhds x.property] with y hy hmem
    simp only [liftExtension, dite_eq_left hmem, cutoffLift,hy]
  ext ⟨i,k⟩
  fin_cases k <;> simp [cutoffDifferential, chartDifferential, CotangentLogCoframe.j,
    HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hext.fderiv_eq]

private theorem ends_antitone {s t : ℝ} (hst : s ≤ t)
    (c : CuspIndex F ζ hζ U R P H) :
    KPContActualCollarBuffer.endSet F ζ hζ U R P H t c ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H s c := by
  rw [← KPContActualCollarBuffer.end_lift_range F ζ hζ U R P H t c, ← KPContActualCollarBuffer.end_lift_range F ζ hζ U R P H s c]
  exact Set.image_mono fun z hz => lt_of_le_of_lt hst hz
private theorem height_tail (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) {s : ℝ} (hs : buf.τ ≤ s) (x : Base F ζ hζ U) :
    x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c ↔
      x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c ∧
        s < KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x := by
  constructor
  · intro hx
    rw [← KPContActualCollarBuffer.end_lift_range F ζ hζ U R P H s c] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [← buf.lift_range c]; exact ⟨z,lt_of_le_of_lt hs hz,rfl⟩
    · rw [buf.height_coordinates c z (lt_of_le_of_lt hs hz)]; exact hz
  · rintro ⟨hx,hheight⟩
    rw [← buf.lift_range c] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    rw [buf.height_coordinates c z hz] at hheight
    rw [← KPContActualCollarBuffer.end_lift_range F ζ hζ U R P H s c]
    exact ⟨z,hheight,rfl⟩
private theorem zero_extension_off (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) {s : ℝ} (hs : buf.τ ≤ s)
    (hφ : ∀ t, t ≤ s → φ t = 0) (x : Base F ζ hζ U)
    (hx : x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c) :
    KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 := by
  by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · have ht : KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x ≤ s := by
      by_contra hn
      exact hx ((height_tail F ζ hζ U R P H D buf c hs x).mpr ⟨he,lt_of_not_ge hn⟩)
    simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he] using hφ _ ht
  · simp [KPContActualCollarBuffer.zeroExtension,he]
private theorem zero_extension_support_tail (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) {s t : ℝ}
    (ht : buf.τ ≤ t) (hts : t < s) (hDs : D ≤ s)
    (hφ : ∀ u, u ≤ s → φ u = 0) :
    tsupport (KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ) ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H t c := by
  intro x hx
  by_contra hnot
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  by_cases hc : x ∈ closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c)
  · by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
    · have ht' : KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x ≤ t := by
        by_contra hn
        exact hnot ((height_tail F ζ hζ U R P H D buf c ht x).mpr ⟨he,lt_of_not_ge hn⟩)
      have hcont := (buf.height_continuous c x he).continuousAt ((buf.open_ends c).mem_nhds he)
      have hsmall := (isOpen_Iio.mem_nhds (lt_of_le_of_lt ht' hts))
      filter_upwards [hcont hsmall, (buf.open_ends c).mem_nhds he] with y hy hmem
      simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hmem,Pi.zero_apply]
      exact hφ _ hy.le
    · have hf : x ∈ frontier (KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) := by
        rw [frontier, (buf.open_ends c).interior_eq]; exact ⟨hc,he⟩
      obtain ⟨V,hV,hxV,hbound⟩ := buf.boundary_height_buffer c x hf
      filter_upwards [hV.mem_nhds hxV] with y hy
      by_cases hyE : y ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
      · simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hyE,Pi.zero_apply]
        exact hφ _ ((hbound y hy hyE).le.trans hDs)
      · simp [KPContActualCollarBuffer.zeroExtension,hyE]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have he : y ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := fun he => hy (subset_closure he)
    simp [KPContActualCollarBuffer.zeroExtension,he]

private theorem differentialSupport_in_core (η : Cutoff F ζ hζ U R P H)
    (B : ℝ) (hp : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c,
      η.val x = r) : differentialSupport F ζ hζ U R P H η ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (KPContActualCollarBuffer.all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  rintro x ⟨a,y,rfl,hy⟩ hx
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r,hr⟩ := hp c
  have he : (fun z => η.val (q a z)) =ᶠ[𝓝 y.val] (fun _ => r) := by
    filter_upwards [((KPContActualCollarBuffer.all_ends_open F ζ hζ U R P H B c).preimage (continuous_chart_projection a)).mem_nhds hc] with z hz
    exact hr _ hz
  exact hy (differential_zero_of_germ F ζ hζ U R P H η a y r he)
private theorem compact_differential_of_end_plateaus (η : Cutoff F ζ hζ U R P H)
    (B : ℝ) (hp : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c,
      η.val x = r) : IsCompact (differentialSupport F ζ hζ U R P H η) :=
  (KPContActualCollarBuffer.compact_truncated_core F ζ hζ U R P H B).of_isClosed_subset isClosed_closure
    (differentialSupport_in_core F ζ hζ U R P H η B hp)

 def subCutoff (η ξ : Cutoff F ζ hζ U R P H) : Cutoff F ζ hζ U R P H :=
  ⟨η.val - ξ.val, fun a => by
    obtain ⟨g,hg,he⟩ := η.smooth a
    obtain ⟨k,hk,hke⟩ := ξ.smooth a
    exact ⟨g-k,hg.sub hk,fun x => by simp only [Pi.sub_apply,he,hke]⟩⟩

private theorem extension_other (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    {c c' : CuspIndex F ζ hζ U R P H} (hcc : c ≠ c') (φ : ℝ → ℝ)
    (x : Base F ζ hζ U) (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c') :
    KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 := by
  have hn : x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := by
    intro hc
    exact Set.disjoint_left.mp (buf.disjoint_ends hcc) hc hx
  simp [KPContActualCollarBuffer.zeroExtension,hn]
private theorem extension_sum_at (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) :
    (∑ c', KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c' φ x) =
      φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) := by
  rw [Finset.sum_eq_single c]
  · simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hx]
  · intro b _ hbc
    exact extension_other F ζ hζ U R P H D buf hbc φ x hx
  · simp
private theorem cutoff_core_support (η : Cutoff F ζ hζ U R P H) (B : ℝ)
    (hp : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → η.val x = 0) :
    tsupport η.val ⊆ (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (KPContActualCollarBuffer.all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  intro x hx hn
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hn
  exact hx (hp c x hc)
private theorem compact_core_from_plateau (η : Cutoff F ζ hζ U R P H) (B : ℝ)
    (hp : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → η.val x = 0) :
    HasCompactSupport η.val :=
  (KPContActualCollarBuffer.compact_truncated_core F ζ hζ U R P H B).of_isClosed_subset (isClosed_tsupport _)
    (cutoff_core_support F ζ hζ U R P H η B hp)

private theorem norm_zero_off_differentialSupport (η : Cutoff F ζ hζ U R P H)
    (x : Base F ζ hζ U) (hx : x ∉ differentialSupport F ζ hζ U R P H η) :
    differentialNormSquared F ζ hζ U R P H η x = 0 := by
  rw [differentialSupport_eq_tsupport] at hx
  exact image_eq_zero_of_notMem_tsupport hx
private theorem error_support_core (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) (B : ℝ)
    (h₀ : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, χ₀.val x = r)
    (hχ : ∀ k c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, (χ k).val x = r) :
    tsupport (collarError F ζ hζ U R P H χ₀ χ) ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (KPContActualCollarBuffer.all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  intro x hx hhigh
  have hn₀ : x ∉ differentialSupport F ζ hζ U R P H χ₀ :=
    fun hh => differentialSupport_in_core F ζ hζ U R P H χ₀ B h₀ hh hhigh
  have hnχ : ∀ k, x ∉ differentialSupport F ζ hζ U R P H (χ k) :=
    fun k hh => differentialSupport_in_core F ζ hζ U R P H (χ k) B (hχ k) hh hhigh
  apply hx
  simp only [collarError, norm_zero_off_differentialSupport F ζ hζ U R P H χ₀ x hn₀,
    norm_zero_off_differentialSupport F ζ hζ U R P H (χ _) x (hnχ _), Finset.sum_const_zero, add_zero]

private theorem closure_end_inside (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (s t : ℝ) (hDs : D ≤ s) (hst : s < t) :
    closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c) ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H s c := by
  let m := (s+t)/2
  let φ := fun u => Real.smoothTransition ((u-m)/(t-m))
  have hsm : s < m := by dsimp [m]; linarith
  have hmt : m < t := by dsimp [m]; linarith
  have hzero : ∀ u, u ≤ m → φ u = 0 := by
    intro u hu
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sub_nonneg.mpr hmt.le))
  apply Set.Subset.trans (closure_mono ?_) (zero_extension_support_tail F ζ hζ U R P H D buf c φ
    (buf.below_cutoff.le.trans hDs) hsm (hDs.trans hsm.le) hzero)
  intro x hx
  have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans (hDs.trans hst.le)) x).mp hx
  change KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x ≠ 0
  simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem hh.1]
  have hone : φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hmt)).mpr (by linarith [hh.2]))
  rw [hone]; exact one_ne_zero
private theorem core_in_open_lower (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (s t : ℝ) (hDs : D ≤ s) (hst : s < t) :
    (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H s c)ᶜ ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c))ᶜ := by
  intro x hx hh
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
  exact hx (Set.mem_iUnion.mpr ⟨c,closure_end_inside F ζ hζ U R P H D buf c s t hDs hst hc⟩)

end ConstructionHelpers

section Constant

def oneCutoff : Cutoff F ζ hζ U R P H :=
  ⟨fun _ => 1, fun a => ⟨fun _ => 1, contDiffOn_const, fun _ => rfl⟩⟩

private theorem oneCutoff_differential (a : ActualChart (U := U) (H := H)) (x : omega a) :
    cutoffDifferential (oneCutoff F ζ hζ U R P H) a x = 0 :=
  differential_zero_of_germ F ζ hζ U R P H _ a x 1 (Filter.EventuallyEq.rfl)

private theorem oneCutoff_norm :
    differentialNormSquared F ζ hζ U R P H (oneCutoff F ζ hζ U R P H) = 0 := by
  symm
  apply (Classical.choose_spec
    (cutoffNorm_descends (oneCutoff F ζ hζ U R P H))).2
  refine ⟨continuous_const, ?_⟩
  intro a x
  simp only [Pi.zero_apply, oneCutoff_differential, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)]

def oneMultiplier : SectorMultiplier F ζ hζ U R P H (oneCutoff F ζ hζ U R P H) where
  op := ContinuousLinearMap.id ℂ _
  ae_apply := fun u => Filter.Eventually.of_forall (fun x => by
    simp only [ContinuousLinearMap.id_apply, oneCutoff, one_mul, Complex.ofReal_one])
  test_commutes := by
    intro f
    have he : scalarMultiply (oneCutoff F ζ hζ U R P H) f = f := by
      apply Subtype.ext
      funext a x
      simp [scalarMultiply, cutoffLift, oneCutoff]
    rw [he]
    rfl
  ordinary_central_invariant := fun _ _ => rfl
  genuine_unchanged := by
    intro f ε x
    simpa only [oneCutoff, Complex.ofReal_one, one_mul,
      KPContSectorCoveredQuotientVocabulary.chi_coe] using f.property ε x

theorem squareEndPartition_no_ends (T : ℝ) [IsEmpty (CuspIndex F ζ hζ U R P H)] :
    Nonempty (SquareEndPartition F ζ hζ U R P H T) := by
  have hcompact : IsCompact (Set.univ : Set (Base F ζ hζ U)) := by
    have hends : (⋃ i : Fin (H.atlas U).componentCount, ⋃ a : Fin ((H.atlas U).cuspAtlas i).cuspCount,
        KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) ''
          KPFiniteCuspAtlas.endSet F
            (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
            (((H.atlas U).cuspAtlas i).representative a) (H.atlas U).threshold) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact isEmptyElim (⟨i,a⟩ : CuspIndex F ζ hζ U R P H)
    simpa only [hends, Set.diff_empty] using (H.atlas U).compact_core
  let η := oneCutoff F ζ hζ U R P H
  let χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H := fun c => isEmptyElim c
  have herror : collarError F ζ hζ U R P H η χ = 0 := by
    funext x
    simp [collarError, η, oneCutoff_norm]
  have hηcompact : HasCompactSupport η.val := by
    apply hcompact.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  exact ⟨{ χ₀ := η, χ := χ, ρ := η
           core_range := fun x => by simp [η, oneCutoff]
           cusp_range := isEmptyElim
           square_sum := fun x => by simp [η, oneCutoff]
           cusp_support_in_tail := isEmptyElim
           error_nonnegative := fun x => by simp [herror]
           error_bounded := ⟨0, le_rfl, fun x => by simp [herror]⟩
           rho_range := fun x => by simp [η, oneCutoff]
           compact_rho_support := hηcompact
           rho_one_neighborhood := ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ _ => rfl⟩
           core_multiplier := oneMultiplier F ζ hζ U R P H
           cusp_multiplier := isEmptyElim
           rho_multiplier := oneMultiplier F ζ hζ U R P H }⟩
end Constant

section RadialConstruction
 def radialCutoff (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hz : ∀ t, t ≤ D → φ t = 0) : Cutoff F ζ hζ U R P H :=
  Classical.choose (KPContActualRadialCutoff.exists_smooth_zero_extension F ζ hζ U R P H D buf c φ hφ hz)
private theorem radialCutoff_val (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hz : ∀ t, t ≤ D → φ t = 0) :
    (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val =
      KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ :=
  (Classical.choose_spec (KPContActualRadialCutoff.exists_smooth_zero_extension F ζ hζ U R P H D buf c φ hφ hz)).1
 def complementRadial (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0) : Cutoff F ζ hζ U R P H :=
  subCutoff F ζ hζ U R P H (oneCutoff F ζ hζ U R P H)
    (sumCutoff F ζ hζ U R P H Finset.univ (fun c => radialCutoff F ζ hζ U R P H D buf c φ hφ hz))
private theorem complementRadial_val (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0) (x : Base F ζ hζ U) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x =
      1 - ∑ c, KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x := by
  simp only [complementRadial,subCutoff,oneCutoff,sumCutoff,Pi.sub_apply,radialCutoff_val]
private theorem complementRadial_on_end (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x =
      1 - φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) := by
  rw [complementRadial_val, extension_sum_at F ζ hζ U R P H D buf φ c x hx]
private theorem complementRadial_one_off (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (s : ℝ) (hs : D ≤ s) (hzs : ∀ t, t ≤ s → φ t = 0) (x : Base F ζ hζ U)
    (hx : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x = 1 := by
  rw [complementRadial_val]
  have he : ∀ c, KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 :=
    fun c => zero_extension_off F ζ hζ U R P H D buf c φ (buf.below_cutoff.le.trans hs) hzs x (hx c)
  simp only [he,Finset.sum_const_zero,sub_zero]
private theorem complementRadial_range (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (hr : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (x : Base F ζ hζ U) :
    0 ≤ (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x ∧
      (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x ≤ 1 := by
  by_cases he : ∃ c, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · obtain ⟨c,hc⟩ := he
    rw [complementRadial_on_end F ζ hζ U R P H D buf φ hφ hz c x hc]
    have := hr (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)
    constructor <;> linarith
  · have hx : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H D c := by
      intro c hc; exact he ⟨c, ends_antitone F ζ hζ U R P H buf.below_cutoff.le c hc⟩
    rw [complementRadial_one_off F ζ hζ U R P H D buf φ hφ hz D le_rfl hz x hx]
    exact ⟨zero_le_one,le_rfl⟩

private theorem complementRadial_high (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (B : ℝ) (hDB : D ≤ B) (hone : ∀ t, B ≤ t → φ t = 1)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x = 0 := by
  have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans hDB) x).mp hx
  rw [complementRadial_on_end F ζ hζ U R P H D buf φ hφ hz c x hh.1, hone _ hh.2.le, sub_self]
private theorem radial_range (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (hr : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U) :
    0 ≤ (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x ∧
      (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x ≤ 1 := by
  rw [radialCutoff_val]
  by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he] using hr (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)
  · simp [KPContActualCollarBuffer.zeroExtension,he]
private theorem radial_plateau (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (B : ℝ) (hDB : D ≤ B) (hone : ∀ t, B ≤ t → φ t = 1)
    (c : CuspIndex F ζ hζ U R P H) :
    ∀ c', ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c',
      (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x = r := by
  intro c'
  by_cases hc : c = c'
  · subst c'
    refine ⟨1,fun x hx => ?_⟩
    rw [radialCutoff_val]
    have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans hDB) x).mp hx
    simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem hh.1]
    exact hone _ hh.2.le
  · refine ⟨0,fun x hx => ?_⟩
    rw [radialCutoff_val]
    exact extension_other F ζ hζ U R P H D buf hc φ x
      (ends_antitone F ζ hζ U R P H (buf.below_cutoff.le.trans hDB) c' hx)

private theorem sin_profile_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t => Real.sin (angle A B t)) :=
  Real.contDiff_sin.comp (angle_smooth A B)
private theorem cos_complement_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t => 1 - Real.cos (angle A B t)) :=
  contDiff_const.sub (Real.contDiff_cos.comp (angle_smooth A B))
private theorem transition_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞)
    (fun t => Real.smoothTransition ((t-A)/(B-A))) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
private theorem cos_complement_zero {A B : ℝ} (hAB : A < B) : ∀ t, t ≤ A → 1 - Real.cos (angle A B t) = 0 := by
  intro t ht; rw [angle_zero hAB ht,Real.cos_zero,sub_self]
private theorem sin_profile_zero {A B : ℝ} (hAB : A < B) : ∀ t, t ≤ A → Real.sin (angle A B t) = 0 := by
  intro t ht; rw [angle_zero hAB ht,Real.sin_zero]
private theorem cos_complement_one {A B : ℝ} (hAB : A < B) : ∀ t, B ≤ t → 1 - Real.cos (angle A B t) = 1 := by
  intro t ht; rw [angle_one hAB ht,Real.cos_pi_div_two,sub_zero]
private theorem sin_profile_one {A B : ℝ} (hAB : A < B) : ∀ t, B ≤ t → Real.sin (angle A B t) = 1 := by
  intro t ht; rw [angle_one hAB ht,Real.sin_pi_div_two]
private theorem cos_complement_range (A B : ℝ) : ∀ t, 0 ≤ 1 - Real.cos (angle A B t) ∧ 1 - Real.cos (angle A B t) ≤ 1 := by
  intro t; have := cos_range A B t; constructor <;> linarith
private theorem square_sum_radial (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (A B : ℝ) (hAB : A < B) (hDA : D ≤ A) (x : Base F ζ hζ U) :
    (complementRadial F ζ hζ U R P H D buf (fun t => 1 - Real.cos (angle A B t))
      (cos_complement_smooth A B) (fun t ht => cos_complement_zero hAB t (ht.trans hDA))).val x ^ 2 +
    ∑ c, (radialCutoff F ζ hζ U R P H D buf c (fun t => Real.sin (angle A B t))
      (sin_profile_smooth A B) (fun t ht => sin_profile_zero hAB t (ht.trans hDA))).val x ^ 2 = 1 := by
  by_cases he : ∃ c, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · obtain ⟨c,hc⟩ := he
    rw [complementRadial_on_end F ζ hζ U R P H D buf _ _ _ c x hc]
    have heq : ∑ k, (radialCutoff F ζ hζ U R P H D buf k (fun t => Real.sin (angle A B t))
        (sin_profile_smooth A B) (fun t ht => sin_profile_zero hAB t (ht.trans hDA))).val x ^ 2 =
        Real.sin (angle A B (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)) ^ 2 := by
      rw [Finset.sum_eq_single c]
      · rw [radialCutoff_val]
        simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hc]
      · intro k _ hkc
        rw [radialCutoff_val,extension_other F ζ hζ U R P H D buf hkc _ x hc]
        norm_num
      · simp
    rw [heq]
    have hid := Real.sin_sq_add_cos_sq (angle A B (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x))
    nlinarith
  · have hn : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := fun c hc => he ⟨c,hc⟩
    rw [complementRadial_val]
    simp only [radialCutoff_val, KPContActualCollarBuffer.zeroExtension,Set.indicator_of_notMem (hn _)]
    norm_num

set_option maxHeartbeats 800000 in
private theorem construct_with_buffer (T : ℝ)
    (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H T) :
    Nonempty (SquareEndPartition F ζ hζ U R P H T) := by
  classical
  let A := T+1
  let B := T+2
  have hTA : T < A := by dsimp [A]; linarith
  have hAB : A < B := by dsimp [A,B]; linarith
  have hTB : T ≤ B := hTA.le.trans hAB.le
  let φ := fun t => Real.sin (angle A B t)
  let ψ := fun t => 1 - Real.cos (angle A B t)
  have hφ := sin_profile_smooth A B
  have hψ := cos_complement_smooth A B
  have hzφ : ∀ t, t ≤ T → φ t = 0 := fun t ht => sin_profile_zero hAB t (ht.trans hTA.le)
  have hzψ : ∀ t, t ≤ T → ψ t = 0 := fun t ht => cos_complement_zero hAB t (ht.trans hTA.le)
  let χ := fun c => radialCutoff F ζ hζ U R P H T buf c φ hφ hzφ
  let χ₀ := complementRadial F ζ hζ U R P H T buf ψ hψ hzψ
  have hcoreRange := complementRadial_range F ζ hζ U R P H T buf ψ hψ hzψ (cos_complement_range A B)
  have hcuspRange := radial_range F ζ hζ U R P H T buf φ hφ hzφ (sin_range A B)
  have hcoreHigh : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → χ₀.val x = 0 :=
    complementRadial_high F ζ hζ U R P H T buf ψ hψ hzψ B hTB (cos_complement_one hAB)
  have hcorePlat : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, χ₀.val x = r :=
    fun c => ⟨0,hcoreHigh c⟩
  have hcuspPlat := radial_plateau F ζ hζ U R P H T buf φ hφ hzφ B hTB (sin_profile_one hAB)
  have hd₀ := compact_differential_of_end_plateaus F ζ hζ U R P H χ₀ B hcorePlat
  have hdχ := fun c => compact_differential_of_end_plateaus F ζ hζ U R P H (χ c) B (hcuspPlat c)
  obtain ⟨-, C, hC, hbound⟩ := collarError_compact_bounded F ζ hζ U R P H χ₀ χ hd₀ hdχ
  let L := B+1
  let M := L+1
  have hBL : B < L := by dsimp [L]; linarith
  have hLM : L < M := by dsimp [M]; linarith
  have hTL : T ≤ L := hTB.trans hBL.le
  let θ := fun t => Real.smoothTransition ((t-L)/(M-L))
  have hθ := transition_smooth L M
  have hzθL : ∀ t, t ≤ L → θ t = 0 := by
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hLM.le))
  have hzθ : ∀ t, t ≤ T → θ t = 0 := fun t ht => hzθL t (ht.trans hTL)
  have honeθ : ∀ t, M ≤ t → θ t = 1 := by
    intro t ht
    exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hLM)).mpr (by linarith))
  let ρ := complementRadial F ζ hζ U R P H T buf θ hθ hzθ
  have hρRange := complementRadial_range F ζ hζ U R P H T buf θ hθ hzθ
    (fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
  have hρHigh := complementRadial_high F ζ hζ U R P H T buf θ hθ hzθ M (hTL.trans hLM.le) honeθ
  obtain ⟨m₀⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H χ₀ 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hcoreRange x).1]; exact (hcoreRange x).2)
  have hmχ := fun c => KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H (χ c) 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hcuspRange c x).1]; exact (hcuspRange c x).2)
  let mχ := fun c => Classical.choice (hmχ c)
  obtain ⟨mρ⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H ρ 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hρRange x).1]; exact (hρRange x).2)
  refine ⟨{ χ₀ := χ₀, χ := χ, ρ := ρ
            core_range := hcoreRange, cusp_range := hcuspRange
            square_sum := square_sum_radial F ζ hζ U R P H T buf A B hAB hTA.le
            cusp_support_in_tail := ?_
            error_nonnegative := (collarError_continuous_nonnegative F ζ hζ U R P H χ₀ χ).2
            error_bounded := ⟨C, hC, hbound⟩
            rho_range := hρRange
            compact_rho_support := compact_core_from_plateau F ζ hζ U R P H ρ M hρHigh
            rho_one_neighborhood := ?_
            core_multiplier := m₀, cusp_multiplier := mχ, rho_multiplier := mρ }⟩
  · intro c
    rw [radialCutoff_val]
    exact zero_extension_support_tail F ζ hζ U R P H T buf c φ buf.below_cutoff.le hTA hTA.le (sin_profile_zero hAB)
  · let V := (⋃ c : CuspIndex F ζ hζ U R P H,
      closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H L c))ᶜ
    refine ⟨V, (isClosed_iUnion_of_finite (fun c => isClosed_closure)).isOpen_compl, ?_, ?_⟩
    · apply Set.Subset.trans _ (core_in_open_lower F ζ hζ U R P H T buf B L hTB hBL)
      exact Set.union_subset
        (cutoff_core_support F ζ hζ U R P H χ₀ B hcoreHigh)
        (error_support_core F ζ hζ U R P H χ₀ χ B hcorePlat hcuspPlat)
    · intro x hx
      apply complementRadial_one_off F ζ hζ U R P H T buf θ hθ hzθ L hTL hzθL x
      intro c hc
      exact hx (Set.mem_iUnion.mpr ⟨c,subset_closure hc⟩)

end RadialConstruction

end DedekindZetaZeroFree.KPContActualSquareEndPartition

namespace DedekindZetaZeroFree

theorem kp_cont_actual_square_end_partition
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (T : ℝ) (hT : KPContActualSquareEndPartition.AboveEndStarts F ζ hζ U R P H T) :
    Nonempty (KPContActualSquareEndPartition.SquareEndPartition F ζ hζ U R P H T) := by
  classical
  by_cases he : IsEmpty (KPContActualSquareEndPartition.CuspIndex F ζ hζ U R P H)
  · letI := he
    exact KPContActualSquareEndPartition.squareEndPartition_no_ends F ζ hζ U R P H T
  · have hc : Nonempty (KPContActualSquareEndPartition.CuspIndex F ζ hζ U R P H) :=
      not_isEmpty_iff.mp he
    obtain ⟨c⟩ := hc
    have hthreshold : (H.atlas U).threshold < T := by
      rw [← (H.atlas U).common_threshold c.1]
      exact hT c
    obtain ⟨buf⟩ := kp_cont_actual_collar_buffer F ζ hζ U R P H realization T hthreshold
    exact KPContActualSquareEndPartition.construct_with_buffer F ζ hζ U R P H T buf

end DedekindZetaZeroFree

end
