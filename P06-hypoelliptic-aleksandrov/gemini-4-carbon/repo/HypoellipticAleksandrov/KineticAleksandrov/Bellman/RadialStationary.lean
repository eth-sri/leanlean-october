module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
public import Mathlib.MeasureTheory.Measure.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Regular
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter Topology

/-- The test lift is the actual positive-radius integral with degree minus one minus alpha. -/
def lift (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∫ r : BellmanPositiveTime, r.val ^ (-1 - alpha) *
    zeta (bellmanPlaneDilation r.val q) ∂bellmanPositiveTimeVolume

/-- Regularity extends across the zero neighborhood of any test supported away from zero. -/
theorem bellman_compact_test_contDiff_order (n : WithTop ℕ∞) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ n zeta bellmanPuncturedSet)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) : ContDiff ℝ n zeta := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q ∈ bellmanPuncturedSet
  · exact (hz q hq).contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)
  · have hn : q ∉ tsupport zeta := fun ht => hq (hs ht)
    have he : zeta =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport zeta).isOpen_compl.mem_nhds hn] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    exact contDiffAt_const.congr_of_eventuallyEq he



/-- A compact test away from zero has a positive lower and finite upper gauge bound. -/
theorem bellman_compact_test_gauge_bounds (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ q ∈ tsupport zeta,
      a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b := by
  by_cases hn : (tsupport zeta).Nonempty
  · obtain ⟨q0, hq0, hlo⟩ := hc.exists_isMinOn hn bellmanGauge_continuous.continuousOn
    obtain ⟨q1, hq1, hhi⟩ := hc.exists_isMaxOn hn bellmanGauge_continuous.continuousOn
    exact ⟨bellmanGauge q0, bellmanGauge q1, bellmanGauge_pos q0 (hs hq0),
      hhi hq0, fun q hq => ⟨hlo hq, hhi hq⟩⟩
  · exact ⟨1, 1, by norm_num, le_rfl, fun q hq => (hn ⟨q, hq⟩).elim⟩

/-- Each punctured spatial point has a neighborhood sharing one compact positive radial window. -/
theorem bellman_compact_test_local_radius_window (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧ U ⊆ bellmanPuncturedSet ∧
      ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
        ∀ x ∈ U, ∀ r : BellmanPositiveTime,
          bellmanPlaneDilation r.val x ∈ tsupport zeta → r.val ∈ Icc a b := by
  obtain ⟨a0, b0, ha0, hab0, hbounds⟩ := bellman_compact_test_gauge_bounds zeta hc hs
  have hg := bellmanGauge_pos q hq
  let U := {x : ℝ × ℝ | bellmanGauge q / 2 < bellmanGauge x ∧
    bellmanGauge x < 2 * bellmanGauge q}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const bellmanGauge_continuous).inter
      (isOpen_lt bellmanGauge_continuous continuous_const)
  have hqU : q ∈ U := ⟨half_lt_self hg, by linarith⟩
  have hsub : U ⊆ bellmanPuncturedSet := by
    intro x hx hz
    have hh := hx.1
    have hzero : bellmanGauge (0, 0) = 0 := by
      norm_num [bellmanGauge, bellmanGaugePower]
    rw [hz, hzero] at hh
    linarith
  refine ⟨U, hU, hqU, hsub, a0 / (2 * bellmanGauge q),
    2 * b0 / bellmanGauge q, div_pos ha0 (by positivity), ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity) hg).mpr
    nlinarith [mul_pos ha0 hg]
  · intro x hx r hr
    obtain ⟨hlo, hhi⟩ := hbounds _ hr
    rw [bellmanGauge_dilation _ r.property] at hlo hhi
    constructor
    · apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_pos r.property (sub_pos.mpr hx.2)]
    · apply (le_div_iff₀ hg).mpr
      nlinarith [mul_pos r.property (sub_pos.mpr hx.1)]


/-- A closed interval of positive radii is compact on the source radial subtype. -/
theorem bellmanRadiusWindow_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact {r : BellmanPositiveTime | r.val ∈ Icc a b} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : BellmanPositiveTime → ℝ) '' {r | r.val ∈ Icc a b} =
      Icc a b := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hr
      exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- Restricting a test to a compact radial window is exactly a subtype integral. -/
theorem bellman_integral_compact_radius_subtype {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (K : Set BellmanPositiveTime) (hK : IsCompact K)
    (f : BellmanPositiveTime → F) (hf : ∀ r, r ∉ K → f r = 0) :
    (∫ r, f r ∂bellmanPositiveTimeVolume) =
      ∫ r : K, f r.val ∂Measure.comap Subtype.val bellmanPositiveTimeVolume := by
  rw [← (MeasurableEmbedding.subtype_coe hK.measurableSet).integral_map,
    map_comap_subtype_coe hK.measurableSet]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

/-- Pullback radial volume is finite on a compact radius window. -/
theorem bellman_radius_window_volume_finite (K : Set BellmanPositiveTime)
    (hK : IsCompact K) :
    IsFiniteMeasure (Measure.comap (Subtype.val : K → BellmanPositiveTime)
      bellmanPositiveTimeVolume) := by
  have hm : IsFiniteMeasure (bellmanPositiveTimeVolume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  let := hm
  have he : Measure.comap (Subtype.val : K → BellmanPositiveTime)
      bellmanPositiveTimeVolume = Measure.comap Subtype.val
      (bellmanPositiveTimeVolume.restrict K) := by
    apply (MeasurableEmbedding.subtype_coe hK.measurableSet).map_injective
    rw [map_comap_subtype_coe hK.measurableSet,
      map_comap_subtype_coe hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_self]
  rw [he]
  infer_instance


/-- Joint C² regularity gives spatial C² regularity after compact radius integration. -/
theorem bellman_joint_contDiff_integral {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] {U : Set E} (hU : IsOpen U)
    (radius : A → ℝ) (hr : Continuous radius) (hrp : ∀ a, 0 < radius a)
    (f : E × ℝ → F) (hf : ContDiffOn ℝ 2 f (U ×ˢ Ioi 0)) :
    ContDiffOn ℝ 2 (fun q => ∫ a, f (q, radius a) ∂mu) U := by
  let L : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod 0
  let J :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let g : E × ℝ → E →L[ℝ] F := fun w => J (fderiv ℝ f w)
  have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hg :=
    J.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hopen (m := 1) (by norm_num))
  -- Pin the first-derivative carrier before elaborating the second derivative.
  let : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  let J' :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let g' : E × ℝ → E →L[ℝ] (E →L[ℝ] F) := fun w => J' (fderiv ℝ g w)
  have hg' :=
    (J'.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen hopen (m := 0) (by norm_num))).continuousOn
  have hmap : MapsTo (fun w => (w.1, radius w.2))
      (U ×ˢ univ) (U ×ˢ Ioi 0) := fun w hw => ⟨hw.1, hrp w.2⟩
  have hcm : Continuous (fun w : E × A => (w.1, radius w.2)) :=
    continuous_fst.prodMk (hr.comp continuous_snd)
  have hd0 : ∀ q ∈ U, ∀ a : A,
      HasFDerivAt (fun x => f (x, radius a)) (g (q, radius a)) q := by
    intro q hq a
    have hd := ((hf (q, radius a) ⟨hq, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hq, hrp a⟩)).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun q => (q, radius a)) L q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (radius a) q)
    exact hd.hasFDerivAt.comp q hc
  have hd1 : ∀ q ∈ U, ∀ a : A,
      HasFDerivAt (fun x => g (x, radius a)) (g' (q, radius a)) q := by
    intro q hq a
    have hd := ((hg (q, radius a) ⟨hq, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hq, hrp a⟩)).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun q => (q, radius a)) L q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (radius a) q)
    exact hd.hasFDerivAt.comp q hc
  exact bellman_compact_parameter_contDiffOn_two mu hU
    (fun q a => f (q, radius a)) (fun q a => g (q, radius a))
    (fun q a => g' (q, radius a)) (hf.continuousOn.comp hcm.continuousOn hmap) (hg.continuousOn.comp hcm.continuousOn hmap) (hg'.comp hcm.continuousOn hmap) hd0 hd1


/-- The joint lift integrand on the ambient plane and positive real radius. -/
def bellmanLiftIntegrand (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (w : (ℝ × ℝ) × ℝ) : ℝ :=
  w.2 ^ (-1 - alpha) * zeta (bellmanPlaneDilation w.2 w.1)

/-- The test gives joint regularity of the same order wherever the radius is positive. -/
theorem bellmanLiftIntegrand_contDiffOn_order (n : WithTop ℕ∞)
    (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiff ℝ n zeta) :
    ContDiffOn ℝ n (bellmanLiftIntegrand alpha zeta) (univ ×ˢ Ioi 0) := by
  have hd : ContDiff ℝ n (fun w : (ℝ × ℝ) × ℝ => bellmanPlaneDilation w.2 w.1) := by
    exact ((contDiff_snd.pow 3).mul (contDiff_fst.fst)).prodMk
      (contDiff_snd.mul (contDiff_fst.snd))
  exact (contDiffOn_snd.rpow_const_of_ne (fun w hw => ne_of_gt hw.2)).mul
    (hz.comp hd).contDiffOn




/-- The spatial derivative of a jointly C¹ integrand passes through its compact radius integral. -/
theorem bellman_joint_integral_fderiv {A : Type*}
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (radius : A → ℝ) (hr : Continuous radius) (hrp : ∀ a, 0 < radius a)
    (f : (ℝ × ℝ) × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (U ×ˢ Ioi 0))
    (q : ℝ × ℝ) (hq : q ∈ U) (e : ℝ × ℝ) :
    fderiv ℝ (fun x => ∫ a, f (x, radius a) ∂mu) q e =
      ∫ a, fderiv ℝ f (q, radius a) (e, 0) ∂mu := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0
  let J : (((ℝ × ℝ) × ℝ) →L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ((ℝ × ℝ) × ℝ) ℝ).flip L
  let g : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun w => J (fderiv ℝ f w)
  have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hg : ContinuousOn g (U ×ˢ Ioi 0) :=
    (J.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hopen (m := 0) (by norm_num))).continuousOn
  have hmap : MapsTo (fun w => (w.1, radius w.2))
      (U ×ˢ univ) (U ×ˢ Ioi 0) := fun w hw => ⟨hw.1, hrp w.2⟩
  have hcm : Continuous (fun w : (ℝ × ℝ) × A => (w.1, radius w.2)) :=
    continuous_fst.prodMk (hr.comp continuous_snd)
  have hc1 := hg.comp hcm.continuousOn hmap
  have hd : ∀ x ∈ U, ∀ a : A,
      HasFDerivAt (fun z => f (z, radius a)) (g (x, radius a)) x := by
    intro x hx a
    have hdf := ((hf (x, radius a) ⟨hx, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hx, hrp a⟩)).differentiableAt (by norm_num)
    have hdc : HasFDerivAt (fun z => (z, radius a)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const (radius a) x)
    exact hdf.hasFDerivAt.comp x hdc
  have ht := bellman_compact_parameter_hasFDerivAt mu hU
    (fun x a => f (x, radius a)) (fun x a => g (x, radius a)) (hf.continuousOn.comp hcm.continuousOn hmap) hc1 hd hq
  rw [ht.fderiv, ContinuousLinearMap.integral_apply
    (bellman_compact_parameter_integrable mu (f := fun x a => g (x, radius a)) hc1 hq)]
  rfl


/-- The first derivative is the integral of the actual dilated test derivative. -/
theorem bellman_lift_fderiv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (e : ℝ × ℝ) :
    fderiv ℝ (lift alpha zeta) q e =
      ∫ r : BellmanPositiveTime, r.val ^ (-1 - alpha) *
        fderiv ℝ zeta (bellmanPlaneDilation r.val q) (bellmanDilationLinear r.val e)
        ∂bellmanPositiveTimeVolume  := by
  have bellmanLiftIntegrand_spatial_fderiv (hz : ContDiff ℝ 1 zeta) (q : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (e : ℝ × ℝ) :
      fderiv ℝ (bellmanLiftIntegrand alpha zeta) (q, r) (e, 0) =
      r ^ (-1 - alpha) * fderiv ℝ zeta (bellmanPlaneDilation r q)
        (bellmanDilationLinear r e) := by
    have hf := bellmanLiftIntegrand_contDiffOn_order 1 alpha zeta hz
    have hd : DifferentiableAt ℝ (bellmanLiftIntegrand alpha zeta) (q, r) :=
      ((hf (q, r) ⟨trivial, hr⟩).contDiffAt
        ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨trivial, hr⟩)).differentiableAt (by norm_num)
    let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0
    have hpair : HasFDerivAt (fun x => (x, r)) L q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const r q)
    have hcomp := hd.hasFDerivAt.comp q hpair
    have hslice := (((hz.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).comp q
      (bellmanDilationLinear r).hasFDerivAt).const_mul (r ^ (-1 - alpha))
    change HasFDerivAt (fun x => bellmanLiftIntegrand alpha zeta (x, r)) _ q at hslice
    have he := congrArg (fun D => D e) (hcomp.unique hslice)
    simpa [L, ContinuousLinearMap.prod_apply, zero_apply, smul_apply, bellmanDilationLinear_apply]
      using he
  have hzglobal := bellman_compact_test_contDiff_order 1 zeta hz hs
  obtain ⟨U, hU, hqU, _, a, b, ha, _, hwindow⟩ :=
    bellman_compact_test_local_radius_window zeta hc hs q hq
  let K : Set BellmanPositiveTime := {r | r.val ∈ Icc a b}
  have hK : IsCompact K := bellmanRadiusWindow_isCompact a b ha
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let mu : Measure K := Measure.comap Subtype.val bellmanPositiveTimeVolume
  let : IsFiniteMeasure mu := bellman_radius_window_volume_finite K hK
  let radius : K → ℝ := fun r => r.val.val
  have hr : Continuous radius := continuous_subtype_val.comp continuous_subtype_val
  have hrp : ∀ r : K, 0 < radius r := fun r => r.val.property
  have he : lift alpha zeta =ᶠ[𝓝 q]
      fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu := by
    filter_upwards [hU.mem_nhds hqU] with x hx
    apply bellman_integral_compact_radius_subtype K hK
    intro r hrK
    have hzero : zeta (bellmanPlaneDilation r.val x) = 0 := by
      by_contra hn
      exact hrK (hwindow x hx r (subset_tsupport zeta hn))
    simp [hzero]
  rw [he.fderiv_eq]
  rw [bellman_joint_integral_fderiv mu hU radius hr hrp
    (bellmanLiftIntegrand alpha zeta) ((bellmanLiftIntegrand_contDiffOn_order 1 alpha zeta hzglobal).mono (prod_mono (subset_univ U) Subset.rfl))
    q hqU e]
  simp_rw [bellmanLiftIntegrand_spatial_fderiv hzglobal _ _ (hrp _)]
  symm
  apply bellman_integral_compact_radius_subtype K hK
  intro r hrK
  have hn : bellmanPlaneDilation r.val q ∉ tsupport zeta :=
    fun ht => hrK (hwindow q hqU r ht)
  rw [fderiv_of_notMem_tsupport ℝ hn]
  simp



/-- The first velocity derivative is the lift of the first test jet with its shifted weight. -/
theorem bellman_lift_dv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ)
    (hq : q ∈ bellmanPuncturedSet) :
    bellmanDv (lift alpha zeta) q = lift (alpha - 1) (bellmanDv zeta) q := by
  rw [bellmanDv, bellman_lift_fderiv alpha zeta hz hc hs q hq, lift]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  have hv : bellmanDilationLinear r.val (0, 1) = r.val • (0, 1) := by
    simp [bellmanDilationLinear, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hv, map_smul, smul_eq_mul, ← mul_assoc]
  have hp : r.val ^ (-1 - alpha) * r.val = r.val ^ (-1 - (alpha - 1)) := by
    nth_rw 2 [← Real.rpow_one r.val]
    rw [← Real.rpow_add r.property]
    congr 1
    ring
  rw [hp]
  rfl



/-- The transport and diffusion tests preserve compact support away from the origin. -/
theorem bellman_radial_stationary_test_properties (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    (Continuous (fun q => q.2 * bellmanDx zeta q) ∧
      HasCompactSupport (fun q => q.2 * bellmanDx zeta q) ∧
      tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ bellmanPuncturedSet) ∧
    (Continuous (bellmanDvv zeta) ∧ HasCompactSupport (bellmanDvv zeta) ∧
      tsupport (bellmanDvv zeta) ⊆ bellmanPuncturedSet) := by
  have hvv := bellman_contDiff_direction (bellman_contDiff_direction hz (0, 1)) (0, 1)
  have hts : tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ tsupport zeta :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
  have hrs : tsupport (bellmanDvv zeta) ⊆ tsupport zeta :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans (tsupport_fderiv_apply_subset ℝ (0, 1))
  exact ⟨⟨continuous_snd.mul (bellman_contDiff_direction hz (1, 0)).continuous,
    hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hs⟩,
    ⟨hvv.continuous, hc.of_isClosed_subset (isClosed_tsupport _) hrs, hrs.trans hs⟩⟩



/-- Positive radial dilation of a unit-gauge point stays away from the origin. -/
theorem sphereRadialPoint_ne_zero {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    bellmanPlaneDilation w.1.val w.2.1.val ≠ (0, 0) :=
  bellmanPlaneDilation_ne_zero w.1.val w.1.property w.2.1.val w.2.1.ne_zero

/-- The radial projection uses the source's anisotropic dilation. -/
def sphereRadialPoint {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    BellmanPuncturedPlane :=
  ⟨bellmanPlaneDilation w.1.val w.2.1.val, sphereRadialPoint_ne_zero w⟩

/-- The radial weight has exponent one minus the homogeneous function degree. -/
def bellmanRadiusWeight (alpha : ℝ) : BellmanPositiveTime → ENNReal :=
  fun r => ENNReal.ofReal (r.val ^ (1 - alpha))

/-- The source's weighted positive radial volume. -/
def bellmanRadiusMeasure (alpha : ℝ) : Measure BellmanPositiveTime :=
  bellmanPositiveTimeVolume.withDensity (bellmanRadiusWeight alpha)

/-- The first radial adjoint measure is the actual radial pushforward. -/
def radialMu {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) :
    Measure BellmanPuncturedPlane :=
  Measure.map sphereRadialPoint ((bellmanRadiusMeasure alpha).prod pi)

/-- The second radial adjoint measure includes the actual diffusion coefficient density. -/
def radialEta {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) :
    Measure BellmanPuncturedPlane :=
  Measure.map sphereRadialPoint (((bellmanRadiusMeasure alpha).prod pi).withDensity
    (fun w => ENNReal.ofReal w.2.2.val))

/-- The radial projection is continuous on its actual product carrier. -/
theorem continuous_sphereRadialPoint (lam Lam : ℝ) :
    Continuous (sphereRadialPoint (lam := lam) (Lam := Lam)) := by
  apply Continuous.subtype_mk
  unfold bellmanPlaneDilation
  fun_prop

/-- The radius coordinate is exactly the gauge of the projected point. -/
theorem sphereRadialPoint_gauge {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    bellmanGauge (sphereRadialPoint w).val = w.1.val := by
  rw [sphereRadialPoint, bellmanGauge_dilation _ w.1.property, w.2.1.property, mul_one]

/-- The radial weight is a measurable function on strictly positive radii. -/
theorem measurable_bellmanRadiusWeight (alpha : ℝ) :
    Measurable (bellmanRadiusWeight alpha) := by
  unfold bellmanRadiusWeight
  exact (ENNReal.continuous_ofReal.comp
    (continuous_subtype_val.rpow_const (fun r => Or.inl r.property.ne'))).measurable

/-- Continuous radial weights are finite on every compact subset of positive radii. -/
instance bellmanRadiusMeasure_finiteOnCompacts (alpha : ℝ) :
    IsFiniteMeasureOnCompacts (bellmanRadiusMeasure alpha) := by
  have hf : Continuous (fun r : BellmanPositiveTime => r.val ^ (1 - alpha)) :=
    continuous_subtype_val.rpow_const (fun r => Or.inl r.property.ne')
  exact bellman_withDensity_finiteOnCompacts bellmanPositiveTimeVolume _ hf

/-- Positive radial weighted volume is sigma finite on the open radius carrier. -/
instance bellmanRadiusMeasure_sigmaFinite (alpha : ℝ) :
    SigmaFinite (bellmanRadiusMeasure alpha) := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance


/-- On the punctured plane the gauge is a continuous positive radius coordinate. -/
def bellmanGaugeRadius (q : BellmanPuncturedPlane) : BellmanPositiveTime :=
  ⟨bellmanGauge q.val, bellmanGauge_pos q.val q.property⟩

/-- The positive gauge radius is continuous. -/
theorem continuous_bellmanGaugeRadius : Continuous bellmanGaugeRadius :=
  (bellmanGauge_continuous.comp continuous_subtype_val).subtype_mk _

/-- The source radial projection is proper because its radius is recovered by the gauge. -/
theorem isProperMap_sphereRadialPoint (lam Lam : ℝ) :
    IsProperMap (sphereRadialPoint (lam := lam) (Lam := Lam)) := by
  apply isProperMap_of_comp_of_t2 (continuous_sphereRadialPoint lam Lam)
    continuous_bellmanGaugeRadius
  have he : bellmanGaugeRadius ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
      Prod.fst := by
    funext w
    exact Subtype.ext (sphereRadialPoint_gauge w)
  rw [he]
  exact isProperMap_fst_of_compactSpace

/-- A proper continuous map preserves finite mass on compact subsets. -/
theorem bellman_proper_map_finiteOnCompacts {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace A] [MeasurableSpace B]
    [BorelSpace A] [BorelSpace B] [T2Space B]
    (f : A → B) (hf : IsProperMap f) (mu : Measure A)
    [IsFiniteMeasureOnCompacts mu] : IsFiniteMeasureOnCompacts (Measure.map f mu) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top

/-- The first radial measure is finite on compact subsets of the punctured plane. -/
instance radialMu_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (radialMu alpha pi) :=
  bellman_proper_map_finiteOnCompacts _ (isProperMap_sphereRadialPoint lam Lam) _

/-- The coefficient-weighted product is finite on compact subsets before projection. -/
theorem bellmanRadialEtaProduct_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (((bellmanRadiusMeasure alpha).prod pi).withDensity
      (fun w => ENNReal.ofReal w.2.2.val)) := by
  have hf : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => w.2.2.val) := by fun_prop
  exact bellman_withDensity_finiteOnCompacts ((bellmanRadiusMeasure alpha).prod pi) _ hf

/-- The second radial measure is finite on compact subsets of the punctured plane. -/
instance radialEta_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (radialEta alpha pi) := by
  let := bellmanRadialEtaProduct_finiteOnCompacts alpha pi
  exact bellman_proper_map_finiteOnCompacts _ (isProperMap_sphereRadialPoint lam Lam) _



/-- Scaling only the radius transforms the product by its literal radial factor. -/
theorem bellman_radial_product_scale {lam Lam : ℝ} (alpha r : ℝ) (hr : 0 < r)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl
      (BellmanSphere × BellmanCoefficient lam Lam)))
      ((bellmanRadiusMeasure alpha).prod pi) =
      ENNReal.ofReal (r ^ (alpha - 2)) • ((bellmanRadiusMeasure alpha).prod pi)  := by
  have map_bellmanRadiusMeasure_radialScale (alpha : ℝ) (r : ℝ) (hr : 0 < r) :
      Measure.map (bellmanRadialScale r hr) (bellmanRadiusMeasure alpha) =
      ENNReal.ofReal (r ^ (alpha - 2)) • bellmanRadiusMeasure alpha := by
    have bellmanRadiusWeight_inverse_scale (s : BellmanPositiveTime) :
        bellmanRadiusWeight alpha ((bellmanRadialScale r hr).symm s) =
        ENNReal.ofReal (r ^ (alpha - 1)) * bellmanRadiusWeight alpha s := by
      change ENNReal.ofReal ((r⁻¹ * s.val) ^ (1 - alpha)) = _
      rw [Real.mul_rpow (inv_nonneg.mpr hr.le) s.property.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
      have he : (r⁻¹) ^ (1 - alpha) = r ^ (alpha - 1) := by
        rw [← Real.rpow_neg_eq_inv_rpow]
        congr 1
        ring
      rw [he]
      rfl
    unfold bellmanRadiusMeasure
    rw [bellman_map_withDensity _ _ _ (measurable_bellmanRadiusWeight alpha),
      map_bellmanPositiveTimeVolume_radialScale]
    have he : (fun s => bellmanRadiusWeight alpha ((bellmanRadialScale r hr).symm s)) =
        ENNReal.ofReal (r ^ (alpha - 1)) • bellmanRadiusWeight alpha :=
      funext (bellmanRadiusWeight_inverse_scale)
    rw [he, withDensity_smul_measure, withDensity_smul _
      (measurable_bellmanRadiusWeight alpha), smul_smul]
    congr 1
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    have hi : r⁻¹ = r ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
    rw [hi, ← Real.rpow_add hr]
    congr 2
    ring
  change Measure.map (Prod.map (bellmanRadialScale r hr) id) _ = _
  rw [← Measure.map_prod_map _ _ (bellmanRadialScale r hr).measurable measurable_id,
    Measure.map_id, map_bellmanRadiusMeasure_radialScale, Measure.prod_smul_left]

/-- The coefficient-weighted product has the same radial scaling factor. -/
theorem bellman_radial_weighted_product_scale {lam Lam : ℝ} (alpha r : ℝ) (hr : 0 < r)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl
      (BellmanSphere × BellmanCoefficient lam Lam)))
      (((bellmanRadiusMeasure alpha).prod pi).withDensity
        (fun w => ENNReal.ofReal w.2.2.val)) =
      ENNReal.ofReal (r ^ (alpha - 2)) •
        (((bellmanRadiusMeasure alpha).prod pi).withDensity
          (fun w => ENNReal.ofReal w.2.2.val)) := by
  have hf : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => ENNReal.ofReal w.2.2.val) := by
    fun_prop
  rw [bellman_map_withDensity _ _ _ hf, bellman_radial_product_scale,
    withDensity_smul_measure]
  rfl





/-- Positive subtype volume is nonzero, as witnessed by its real pushforward. -/
theorem bellmanPositiveTimeVolume_ne_zero : bellmanPositiveTimeVolume ≠ 0 := by
  intro hz
  have hm := map_bellmanPositiveTimeVolume_coe
  rw [hz, Measure.map_zero] at hm
  have he := congrArg (fun mu : Measure ℝ => mu (Icc 1 2)) hm
  have hi : Icc (1 : ℝ) 2 ∩ Ioi 0 = Icc 1 2 :=
    inter_eq_left.mpr (fun x hx => lt_of_lt_of_le (by norm_num) hx.1)
  norm_num [Measure.restrict_apply measurableSet_Icc, hi] at he






/-- Compact radial support proves integrability, including any continuous coefficient weight. -/
theorem bellman_radial_test_integrable {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi]
    (g : (ℝ × ℝ) → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ bellmanPuncturedSet)
    (weight : BellmanSphere × BellmanCoefficient lam Lam → ℝ) (hw : Continuous weight) :
    Integrable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) =>
      w.1.val ^ (1 - alpha) * (weight w.2 * g (sphereRadialPoint w).val))
      (bellmanPositiveTimeVolume.prod pi)  := by
  have bellman_radial_test_compactSupport :
      HasCompactSupport (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) =>
      w.1.val ^ (1 - alpha) * (weight w.2 * g (sphereRadialPoint w).val)) := by
    obtain ⟨a, b, ha, _, hbounds⟩ := bellman_compact_test_gauge_bounds g hc hs
    have hK := (bellmanRadiusWindow_isCompact a b ha).prod
      (isCompact_univ : IsCompact (univ : Set (BellmanSphere × BellmanCoefficient lam Lam)))
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal
    · intro w hw
      have hg : g (sphereRadialPoint w).val ≠ 0 := by
        intro hz
        exact hw (by simp [hz])
      have hb := hbounds _ (subset_tsupport g hg)
      rw [sphereRadialPoint_gauge] at hb
      exact ⟨hb, trivial⟩
    · exact hK.isClosed
  have hr : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => w.1.val ^ (1 - alpha)) :=
    (continuous_subtype_val.comp continuous_fst).rpow_const
      (fun w => Or.inl w.1.property.ne')
  have hp : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => (sphereRadialPoint w).val) :=
    continuous_subtype_val.comp (continuous_sphereRadialPoint lam Lam)
  exact (hr.mul ((hw.comp continuous_snd).mul (hg.comp hp))).integrable_of_hasCompactSupport
    (bellman_radial_test_compactSupport)



/-- Integrating the second radial measure also retains the literal coefficient weight. -/
theorem integral_radialEta {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi]
    (f : BellmanPuncturedPlane → ℝ) (hf : Continuous f) (hlam : 0 ≤ lam) :
    (∫ q, f q ∂radialEta alpha pi) =
      ∫ w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam),
        w.1.val ^ (1 - alpha) * (w.2.2.val * f (sphereRadialPoint w))
        ∂bellmanPositiveTimeVolume.prod pi := by
  unfold radialEta
  rw [integral_map (continuous_sphereRadialPoint lam Lam).measurable.aemeasurable
    hf.aestronglyMeasurable]
  have hcoeff : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => ENNReal.ofReal w.2.2.val) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hcoeff
    (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
  have hweight : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => bellmanRadiusWeight alpha w.1) :=
    (measurable_bellmanRadiusWeight alpha).comp measurable_fst
  unfold bellmanRadiusMeasure
  rw [prod_withDensity_left (measurable_bellmanRadiusWeight alpha),
    integral_withDensity_eq_integral_toReal_smul
      hweight
      (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp [bellmanRadiusWeight, ENNReal.toReal_ofReal (Real.rpow_nonneg w.1.property.le _), ENNReal.toReal_ofReal (hlam.trans w.2.2.property.1)]


/-- An annihilating sphere probability makes the actual radial measures stationary. -/
theorem radial_bellman_pair_stationary (lam Lam alpha : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (ha : 0 < alpha) (ha1 : alpha < 1)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsProbabilityMeasure pi]
    (hann : ∀ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi →
      (∫ w, bellmanOperator w.2.val phi w.1.val ∂pi) = 0) :
    IsBellmanAdjointPair lam Lam (2 + alpha) (radialMu alpha pi) (radialEta alpha pi)       := by
  have bellman_lift_operator_integral (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (b : ℝ) :
      bellmanOperator b (lift alpha zeta) q =
      ∫ r : BellmanPositiveTime,
        (r.val ^ (1 - alpha) *
          ((bellmanPlaneDilation r.val q).2 * bellmanDx zeta
            (bellmanPlaneDilation r.val q))) +
        (r.val ^ (1 - alpha) * (b * bellmanDvv zeta (bellmanPlaneDilation r.val q)))
        ∂bellmanPositiveTimeVolume := by
    have bellman_lift_dvv (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
        bellmanDvv (lift alpha zeta) q = lift (alpha - 2) (bellmanDvv zeta) q := by
      have hv : ContDiffOn ℝ 1 (bellmanDv zeta) bellmanPuncturedSet :=
        (hz.fderiv_of_isOpen bellmanPuncturedSet_isOpen (m := 1) (by norm_num)).clm_apply
          contDiffOn_const
      have he : bellmanDv (lift alpha zeta) =ᶠ[𝓝 q] lift (alpha - 1) (bellmanDv zeta) := by
        filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with x hx
        exact bellman_lift_dv alpha zeta (hz.of_le (by norm_num)) hc hs x hx
      change fderiv ℝ (bellmanDv (lift alpha zeta)) q (0, 1) = _
      rw [he.fderiv_eq]
      change bellmanDv (lift (alpha - 1) (bellmanDv zeta)) q = _
      rw [bellman_lift_dv (alpha - 1) (bellmanDv zeta) hv (hc.fderiv_apply ℝ (0, 1))
        ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hs) q hq]
      have heq : alpha - 1 - 1 = alpha - 2 := by ring
      rw [heq]
      rfl
    have bellman_lift_dx (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
        bellmanDx (lift alpha zeta) q = lift (alpha - 3) (bellmanDx zeta) q := by
      rw [bellmanDx, bellman_lift_fderiv alpha zeta hz hc hs q hq, lift]
      apply integral_congr_ae
      apply ae_of_all
      intro r
      dsimp only
      have hv : bellmanDilationLinear r.val (1, 0) = r.val ^ 3 • (1, 0) := by
        simp [bellmanDilationLinear, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      rw [hv, map_smul, smul_eq_mul, ← mul_assoc]
      have hp : r.val ^ (-1 - alpha) * r.val ^ 3 = r.val ^ (-1 - (alpha - 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add r.property]
        congr 1
        ring
      rw [hp]
      rfl
    have bellman_lift_integrand_integrable (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ) (hz : Continuous zeta) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
        Integrable (fun r => r.val ^ (-1 - alpha) *
        zeta (bellmanPlaneDilation r.val q)) bellmanPositiveTimeVolume := by
      have bellman_lift_integrand_compactSupport :
          HasCompactSupport (fun r : BellmanPositiveTime => r.val ^ (-1 - alpha) *
          zeta (bellmanPlaneDilation r.val q)) := by
        obtain ⟨U, _, hqU, _, a, b, ha, _, hwindow⟩ :=
          bellman_compact_test_local_radius_window zeta hc hs q hq
        have hK := bellmanRadiusWindow_isCompact a b ha
        apply hK.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal
        · intro r hr
          have hz : zeta (bellmanPlaneDilation r.val q) ≠ 0 := by
            intro he
            exact hr (by simp [he])
          exact hwindow q hqU r (subset_tsupport zeta hz)
        · exact hK.isClosed
      have hd : Continuous (fun r : BellmanPositiveTime => bellmanPlaneDilation r.val q) := by
        unfold bellmanPlaneDilation
        fun_prop
      have hcont : Continuous (fun r : BellmanPositiveTime =>
          r.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val q)) :=
        (continuous_subtype_val.rpow_const
        (fun r : BellmanPositiveTime => Or.inl r.property.ne')).mul (hz.comp hd)
      exact hcont.integrable_of_hasCompactSupport
        (bellman_lift_integrand_compactSupport)
    obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
      bellman_radial_stationary_test_properties zeta hz hc hs
    have hiT := bellman_lift_integrand_integrable (alpha - 2)
      (fun q => q.2 * bellmanDx zeta q) ht htc hts
    have hiV := (bellman_lift_integrand_integrable (alpha - 2)
      (bellmanDvv zeta) hv hvc hvs).const_mul b
    have he : -1 - (alpha - 2) = 1 - alpha := by ring
    rw [he] at hiT hiV
    have hiV' : Integrable (fun r : BellmanPositiveTime => r.val ^ (1 - alpha) *
        (b * bellmanDvv zeta (bellmanPlaneDilation r.val q))) bellmanPositiveTimeVolume :=
      hiV.congr (ae_of_all _ (fun r => by ring))
    rw [integral_add hiT hiV', bellmanOperator,
      bellman_lift_dx (hz.of_le (by norm_num)).contDiffOn hc hs q hq,
      bellman_lift_dvv (hz.of_le (by norm_num)).contDiffOn hc hs q hq]
    unfold lift
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    · apply integral_congr_ae
      apply ae_of_all
      intro r
      dsimp only [bellmanPlaneDilation]
      have hp : r.val ^ (-1 - (alpha - 3)) = r.val ^ (1 - alpha) * r.val := by
        calc
          r.val ^ (-1 - (alpha - 3)) = r.val ^ ((1 - alpha) + 1) := by congr 1; ring
          _ = r.val ^ (1 - alpha) * r.val ^ 1 := Real.rpow_add r.property _ _
          _ = r.val ^ (1 - alpha) * r.val := by rw [Real.rpow_one]
      rw [hp]
      ring
    · apply integral_congr_ae
      exact ae_of_all _ (fun r => by rw [he]; ring)
  have bellman_lift_contDiffOn (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
      ContDiffOn ℝ 2 (lift alpha zeta) bellmanPuncturedSet := by
    have bellmanLiftIntegrand_contDiffOn (hz : ContDiff ℝ 2 zeta) : ContDiffOn ℝ 2 (bellmanLiftIntegrand alpha zeta) (univ ×ˢ Ioi 0) :=
      bellmanLiftIntegrand_contDiffOn_order 2 alpha zeta hz
    have hzglobal := (bellman_compact_test_contDiff_order 2 zeta hz hs)
    intro q hq
    obtain ⟨U, hU, hqU, _, a, b, ha, _, hwindow⟩ :=
      bellman_compact_test_local_radius_window zeta hc hs q hq
    let K : Set BellmanPositiveTime := {r | r.val ∈ Icc a b}
    have hK := bellmanRadiusWindow_isCompact a b ha
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let mu : Measure K := Measure.comap Subtype.val bellmanPositiveTimeVolume
    let : IsFiniteMeasure mu := bellman_radius_window_volume_finite K hK
    let radius : K → ℝ := fun r => r.val.val
    have hr : Continuous radius := continuous_subtype_val.comp continuous_subtype_val
    have hrp : ∀ r : K, 0 < radius r := fun r => r.val.property
    have hI : ContDiffOn ℝ 2
        (fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu) U :=
      bellman_joint_contDiff_integral mu hU radius hr hrp
        (bellmanLiftIntegrand alpha zeta) ((bellmanLiftIntegrand_contDiffOn hzglobal).mono (prod_mono (subset_univ U) Subset.rfl))
    have he : lift alpha zeta =ᶠ[𝓝 q]
        fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu := by
      filter_upwards [hU.mem_nhds hqU] with x hx
      apply bellman_integral_compact_radius_subtype K hK
      intro r hrK
      have hzero : zeta (bellmanPlaneDilation r.val x) = 0 := by
        by_contra hn
        exact hrK (hwindow x hx r (subset_tsupport zeta hn))
      simp [hzero]
    have hAt : ContDiffAt ℝ 2 (lift alpha zeta) q :=
      ((hI q hqU).contDiffAt (hU.mem_nhds hqU)).congr_of_eventuallyEq he
    exact hAt.contDiffWithinAt
  have bellman_radial_projection_commute (r : ℝ) (hr : 0 < r) :
      bellmanDilation r hr ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
      sphereRadialPoint ∘ ((bellmanRadialScale r hr).prodCongr
        (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))) := by
    funext w
    apply Subtype.ext
    exact bellmanPlaneDilation_comp r w.1.val w.2.1.val
  have integral_radialMu [IsFiniteMeasure pi] (f : BellmanPuncturedPlane → ℝ) (hf : Continuous f) :
      (∫ q, f q ∂radialMu alpha pi) =
      ∫ w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam),
        w.1.val ^ (1 - alpha) * f (sphereRadialPoint w)
        ∂bellmanPositiveTimeVolume.prod pi := by
    unfold radialMu
    rw [integral_map (continuous_sphereRadialPoint lam Lam).measurable.aemeasurable
      hf.aestronglyMeasurable]
    have hweight : Measurable (fun w : BellmanPositiveTime ×
        (BellmanSphere × BellmanCoefficient lam Lam) => bellmanRadiusWeight alpha w.1) :=
      (measurable_bellmanRadiusWeight alpha).comp measurable_fst
    unfold bellmanRadiusMeasure
    rw [prod_withDensity_left (measurable_bellmanRadiusWeight alpha),
      integral_withDensity_eq_integral_toReal_smul
        hweight
        (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    apply ae_of_all
    intro w
    simp [bellmanRadiusWeight, ENNReal.toReal_ofReal (Real.rpow_nonneg w.1.property.le _)]
  have radial_bellman_measure_properties (_hlam : 0 < lam) (_hLam : lam ≤ Lam) (_ha : 0 < alpha) (_ha1 : alpha < 1) [IsProbabilityMeasure pi] :
      IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) ∧
      (radialMu alpha pi ≠ 0 ∨ radialEta alpha pi ≠ 0) ∧
      ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
      radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi ∧
      HasBellmanDensityDegree (2 + alpha) (radialMu alpha pi) ∧
      HasBellmanDensityDegree (2 + alpha) (radialEta alpha pi) := by
    have radialMu_ne_zero :
        radialMu alpha pi ≠ 0 := by
      intro hz
      have radialMu_radius_marginal :
          Measure.map bellmanGaugeRadius (radialMu alpha pi) = bellmanRadiusMeasure alpha := by
        unfold radialMu
        rw [Measure.map_map continuous_bellmanGaugeRadius.measurable
          (continuous_sphereRadialPoint lam Lam).measurable]
        have he : bellmanGaugeRadius ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
            Prod.fst := by
          funext w
          exact Subtype.ext (sphereRadialPoint_gauge w)
        rw [he, Measure.map_fst_prod, measure_univ, one_smul]
      have bellmanRadiusMeasure_ne_zero :
          bellmanRadiusMeasure alpha ≠ 0 := by
        intro hz
        have hf : ∀ r : BellmanPositiveTime, bellmanRadiusWeight alpha r ≠ 0 := by
          intro r
          exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos r.property _))
        have hempty : ∅ ∈ ae bellmanPositiveTimeVolume := by
          filter_upwards [((withDensity_eq_zero_iff (measurable_bellmanRadiusWeight alpha).aemeasurable).mp hz)] with r hr
          exact (hf r hr).elim
        exact bellmanPositiveTimeVolume_ne_zero (by
          apply MeasureTheory.ae_eq_bot.mp
          exact Filter.empty_mem_iff_bot.mp hempty)
      have hm := radialMu_radius_marginal
      rw [hz, Measure.map_zero] at hm
      exact bellmanRadiusMeasure_ne_zero hm.symm
    have radialEta_densityDegree [IsFiniteMeasure pi] :
        HasBellmanDensityDegree (2 + alpha) (radialEta alpha pi) := by
      apply bellman_degree_of_map_dilation
      intro r hr
      unfold radialEta
      have hf := (continuous_sphereRadialPoint lam Lam).measurable
      have hd := (bellmanDilationHomeomorph r hr).measurable
      change Measurable (bellmanDilation r hr) at hd
      rw [Measure.map_map hd hf,
        bellman_radial_projection_commute,
        ← Measure.map_map hf ((bellmanRadialScale r hr).prodCongr
          (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))).measurable,
        bellman_radial_weighted_product_scale, Measure.map_smul _ hf.aemeasurable]
      have he : 2 + alpha - 4 = alpha - 2 := by ring
      rw [he]
    have radialMu_densityDegree [IsFiniteMeasure pi] :
        HasBellmanDensityDegree (2 + alpha) (radialMu alpha pi) := by
      apply bellman_degree_of_map_dilation
      intro r hr
      unfold radialMu
      have hf := (continuous_sphereRadialPoint lam Lam).measurable
      have hd := (bellmanDilationHomeomorph r hr).measurable
      change Measurable (bellmanDilation r hr) at hd
      rw [Measure.map_map hd hf,
        bellman_radial_projection_commute,
        ← Measure.map_map hf ((bellmanRadialScale r hr).prodCongr
          (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))).measurable,
        bellman_radial_product_scale, Measure.map_smul _ hf.aemeasurable]
      have he : 2 + alpha - 4 = alpha - 2 := by ring
      rw [he]
    have radial_bellman_measures_comparison :
        ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
        radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi := by
      let mu := (bellmanRadiusMeasure alpha).prod pi
      have hlo : ENNReal.ofReal lam • mu ≤
          mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) := by
        rw [← withDensity_const]
        exact withDensity_mono (Filter.Eventually.of_forall
          (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.1))
      have hhi : mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) ≤
          ENNReal.ofReal Lam • mu := by
        rw [← withDensity_const]
        exact withDensity_mono (Filter.Eventually.of_forall
          (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.2))
      have hf := (continuous_sphereRadialPoint lam Lam).measurable
      have hl := Measure.map_mono hlo hf
      have hh := Measure.map_mono hhi hf
      rw [Measure.map_smul _ hf.aemeasurable] at hl hh
      exact ⟨hl, hh⟩
    have radial_bellman_measures_radon [IsFiniteMeasure pi] :
        IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) := by
      let : LocallyCompactSpace BellmanPuncturedPlane :=
        isOpen_compl_singleton.locallyCompactSpace
      exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩
    obtain ⟨hm, he⟩ := radial_bellman_measures_radon
    obtain ⟨hlo, hhi⟩ := radial_bellman_measures_comparison
    exact ⟨hm, he, Or.inl (radialMu_ne_zero), hlo, hhi,
      radialMu_densityDegree, radialEta_densityDegree⟩
  have bellman_test_lift (_ha : 0 < alpha) (_ha1 : alpha < 1) (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
      IsBellmanHomogeneous alpha (lift alpha zeta) ∧
      ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet, ∀ b : ℝ,
        bellmanOperator b (fun z => zeta (bellmanPlaneDilation r z)) q =
          r ^ 2 * bellmanOperator b zeta (bellmanPlaneDilation r q) := by
    have bellman_lift_scaling (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ) :
        lift alpha zeta (bellmanPlaneDilation s q) = s ^ alpha * lift alpha zeta q := open MeasureTheory in by
      let F : BellmanPositiveTime → ℝ := fun r =>
        r.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val q)
      have he (r : BellmanPositiveTime) :
          F (bellmanRadialScale s hs r) = s ^ (-1 - alpha) *
            (r.val ^ (-1 - alpha) *
              zeta (bellmanPlaneDilation r.val (bellmanPlaneDilation s q))) := by
        dsimp [F, bellmanRadialScale]
        rw [Real.mul_rpow hs.le r.property.le, bellmanPlaneDilation_comp]
        rw [mul_comm r.val s]
        ring
      apply mul_left_cancel₀ (Real.rpow_pos_of_pos hs (-1 - alpha)).ne'
      calc
        s ^ (-1 - alpha) * lift alpha zeta (bellmanPlaneDilation s q) =
            ∫ r, F (bellmanRadialScale s hs r) ∂bellmanPositiveTimeVolume := by
          simp_rw [he]
          rw [integral_const_mul]
          rfl
        _ = s⁻¹ * lift alpha zeta q := by
          rw [← (bellmanRadialScale s hs).measurableEmbedding.integral_map,
            map_bellmanPositiveTimeVolume_radialScale, integral_smul_measure,
            ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le)]
          rfl
        _ = s ^ (-1 - alpha) * (s ^ alpha * lift alpha zeta q) := by
          rw [← mul_assoc, ← Real.rpow_add hs]
          have ha : -1 - alpha + alpha = (-1 : ℝ) := by ring
          rw [ha, Real.rpow_neg_one]
    refine ⟨⟨bellman_lift_contDiffOn zeta hz hc hs, ?_⟩, ?_⟩
    · intro r hr q _
      exact bellman_lift_scaling r hr q
    · intro r hr q hq b
      exact bellmanOperator_comp_dilation r hr zeta hz q hq b
  obtain ⟨hm, he, hn, hlo, hhi, hdm, hde⟩ :=
    radial_bellman_measure_properties hlam hLam ha ha1
  refine ⟨hm, he, hn, hlo, hhi, ?_, hdm, hde⟩
  intro zeta hz hc hs
  obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
    bellman_radial_stationary_test_properties zeta hz hc hs
  let FT : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
    fun w => w.1.val ^ (1 - alpha) *
      ((sphereRadialPoint w).val.2 * bellmanDx zeta (sphereRadialPoint w).val)
  let FV : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
    fun w => w.1.val ^ (1 - alpha) *
      (w.2.2.val * bellmanDvv zeta (sphereRadialPoint w).val)
  have hFT : Integrable FT (bellmanPositiveTimeVolume.prod pi) := by
    simpa using bellman_radial_test_integrable alpha pi
      (fun q => q.2 * bellmanDx zeta q) ht htc hts (fun _ => 1) continuous_const
  have hFV : Integrable FV (bellmanPositiveTimeVolume.prod pi) :=
    bellman_radial_test_integrable alpha pi (bellmanDvv zeta) hv hvc hvs
      (fun w => w.2.val) (continuous_subtype_val.comp continuous_snd)
  have hMT : (∫ q, q.val.2 * fderiv ℝ zeta q.val (1, 0) ∂radialMu alpha pi) =
      ∫ w, FT w ∂bellmanPositiveTimeVolume.prod pi :=
    integral_radialMu (fun q => q.val.2 * bellmanDx zeta q.val)
      (ht.comp continuous_subtype_val)
  have hMV : (∫ q, fderiv ℝ (fun z => fderiv ℝ zeta z (0, 1)) q.val (0, 1)
      ∂radialEta alpha pi) = ∫ w, FV w ∂bellmanPositiveTimeVolume.prod pi :=
    integral_radialEta alpha pi (fun q => bellmanDvv zeta q.val)
      (hv.comp continuous_subtype_val) hlam.le
  rw [hMT, hMV, ← integral_add hFT hFV,
    integral_prod_symm (fun w => FT w + FV w) (hFT.add hFV)]
  have hLift : IsBellmanHomogeneous alpha (lift alpha zeta) :=
    (bellman_test_lift ha ha1 zeta (hz.of_le (by norm_num)).contDiffOn hc hs).1
  calc
    (∫ w, ∫ r, FT (r, w) + FV (r, w) ∂bellmanPositiveTimeVolume ∂pi) =
        ∫ w, bellmanOperator w.2.val (lift alpha zeta) w.1.val ∂pi := by
      apply integral_congr_ae
      apply ae_of_all
      intro w
      exact (bellman_lift_operator_integral zeta hz hc hs w.1.val w.1.ne_zero
        w.2.val).symm
    _ = 0 := hann (lift alpha zeta) hLift

end HypoellipticAleksandrov.KineticAleksandrov

