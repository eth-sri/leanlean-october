module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Topology.Order.IntermediateValue
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Round product boxes are open. -/
theorem isOpen_roundBox (d : ℕ) (a b R : ℝ) : IsOpen (roundBox d a b R) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall 0 R).preimage continuous_position).inter
        ((PDE.isOpen_euclideanBall 0 1).preimage continuous_velocity)))

/-- Exact volume of a product box in the coordinate measure. -/
theorem volume_roundBox (d : ℕ) (a b : ℝ) {R : ℝ} (hR : 0 < R) :
    volume (roundBox d a b R) = ENNReal.ofReal (b-a)*ENNReal.ofReal (R^d)*
      volume (unitCylinder d) := by
  let s := Ioo a b ×ˢ (PDE.euclideanBall (0 : PDE.Vec d) R ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) 1)
  have hs : MeasurableSet s := measurableSet_Ioo.prod
    ((PDE.measurableSet_euclideanBall _ _).prod (PDE.measurableSet_euclideanBall _ _))
  have heq : roundBox d a b R = (KineticPoint.equivProd d) ⁻¹' s := by
    ext X
    simp only [roundBox, s, mem_preimage, mem_prod, mem_Ioo, mem_ofPred_eq,
      KineticPoint.equivProd, Equiv.coe_fn_mk, and_assoc]
  have hunit : volume (unitCylinder d) =
      volume (PDE.euclideanBall (0 : PDE.Vec d) 1)*
        volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
    rw [unitCylinder, volume_cylinder_product _ zero_lt_one]
    simp only [one_pow, ENNReal.ofReal_one, one_mul]
  rw [heq, (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet]
  rw [show s = Ioo a b ×ˢ (PDE.euclideanBall (0 : PDE.Vec d) R ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) 1) from rfl]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, PDE.volume_euclideanBall_eq_unit_mul_of_pos _ hR, hunit]
  ring


/-- Real volume formula for a nonempty round product box. -/
theorem volume_roundBox_toReal (d : ℕ) {a b R : ℝ} (hab : a ≤ b) (hR : 0 < R) :
    (volume (roundBox d a b R)).toReal = (b-a)*R^d*(volume (unitCylinder d)).toReal := by
  rw [volume_roundBox d a b hR, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ENNReal.toReal_ofReal (by positivity)]


/-- Linear excess volume of the stack envelope for h between zero and one. -/
theorem leakage_envelope_volume {d : ℕ} {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    (volume (roundBox d (-1) h (1+4*h))).toReal ≤
      (volume (unitCylinder d)).toReal+
        (2*(5 : ℝ)^d)*(volume (unitCylinder d)).toReal*h  := by
  have one_add_four_mul_pow_le {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
      (1+4*h)^d ≤ 1+((5 : ℝ)^d-1)*h := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ, pow_succ]
      have hpow : 1 ≤ (5 : ℝ)^d := one_le_pow₀ (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ 1+4*h)
      have hs : h^2 ≤ h := by nlinarith
      nlinarith
  rw [volume_roundBox_toReal d (by linarith) (by positivity)]
  have hp := one_add_four_mul_pow_le h0.le h1
  have hv := ENNReal.toReal_nonneg (a := volume (unitCylinder d))
  have hpow : 1 ≤ (5 : ℝ)^d := one_le_pow₀ (by norm_num)
  have hs : h^2 ≤ h := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ h-(-1))
  have hpoly : (h-(-1))*(1+4*h)^d ≤ 1+2*(5 : ℝ)^d*h := by nlinarith
  nlinarith only [mul_le_mul_of_nonneg_right hpoly hv]


/-- Finite-volume subtraction for a null-measurable subset. -/
theorem volume_sdiff_toReal_of_subset {d : ℕ} {A B : Set (KineticPoint d)}
    (hB : NullMeasurableSet B volume) (hBA : B ⊆ A) (hA : volume A ≠ ⊤) :
    (volume (A \ B)).toReal = (volume A).toReal-(volume B).toReal := by
  have hBn : volume B ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono hBA)
  have hDn : volume (A \ B) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono sdiff_subset)
  have hs := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) A hB)
  rw [inter_eq_right.mpr hBA, ENNReal.toReal_add hBn hDn] at hs
  linarith

/-- The spatial core whose complement is charged in the critical-cylinder proof. -/
def spatialCore (d : ℕ) (R : ℝ) : Set (KineticPoint d) := roundBox d (-1) 0 (1-2*R^2)

/-- The spatial core is contained in the unit cylinder for small positive cutoff. -/
theorem spatialCore_subset_unit (d : ℕ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1/4) :
    spatialCore d R ⊆ unitCylinder d := by
  have hrad : 0 < 1-2*R^2 := by nlinarith
  intro X hX
  apply (mem_unitCylinder_iff X).mpr
  refine ⟨hX.1, hX.2.1, ?_, ?_⟩
  · simpa only [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
      using hX.2.2.2
  · have hp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrad).mp hX.2.2.1
    rw [sub_zero] at hp
    nlinarith [sq_nonneg R]

/-- The excluded spatial layer costs at most twice dimension times unit volume times R². -/
theorem spatial_shell_volume (d : ℕ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1/4) :
    (volume (unitCylinder d \ spatialCore d R)).toReal ≤
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2  := by
  have one_sub_pow_lower {z : ℝ} (_hz : 0 ≤ z) (hz1 : z ≤ 1) :
      1-(d : ℝ)*z ≤ (1-z)^d := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ]
      push_cast
      have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hz1)
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith [mul_nonneg hd (sq_nonneg z)]
  have hrad : 0 < 1-2*R^2 := by nlinarith
  have hcore : NullMeasurableSet (spatialCore d R) volume :=
    (isOpen_roundBox d (-1) 0 (1-2*R^2)).measurableSet.nullMeasurableSet
  rw [volume_sdiff_toReal_of_subset hcore
    (spatialCore_subset_unit d hR hRsmall)
    (volume_cylinder_pos_ne_top _ zero_lt_one).2]
  rw [spatialCore, volume_roundBox_toReal d (by norm_num) hrad]
  have hp := one_sub_pow_lower (by positivity : 0 ≤ 2*R^2)
    (by nlinarith : 2*R^2 ≤ 1)
  have hv := ENNReal.toReal_nonneg (a := volume (unitCylinder d))
  nlinarith only [mul_le_mul_of_nonneg_right hp hv]



end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
open Set MeasureTheory Filter
open scoped Topology


/-- A strict comparison of continuous real functions is locally constant away from equality. -/
theorem eventually_lt_iff_of_ne {f g : ℝ → ℝ} {r : ℝ}
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) (hne : f r ≠ g r) :
    ∀ᶠ s in 𝓝 r, f s < g s ↔ f r < g r := by
  by_cases h : f r < g r
  · filter_upwards [hf.eventually_lt hg h] with s hs
    exact ⟨fun _ => h, fun _ => hs⟩
  · have hgt : g r < f r := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    filter_upwards [hg.eventually_lt hf hgt] with s hs
    exact ⟨fun hlt => (not_lt_of_ge hs.le hlt).elim, fun hlt => (h hlt).elim⟩

/-- A null equality fiber is avoided almost everywhere. -/
theorem ae_ne_of_null_fiber {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (c : ℝ) (h : μ {x | f x = c} = 0) : ∀ᵐ x ∂μ, f x ≠ c := by
  simpa only [ae_iff, not_not] using h


/-- Intersection volume with any finite-volume set is continuous along continuous centers. -/
theorem continuousAt_cylinder_inter_volume {d : ℕ} (P : ℝ → KineticPoint d)
    (hP : Continuous P) {E : Set (KineticPoint d)} (hE : volume E ≠ ⊤)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun s => (volume (E ∩ backwardCylinder (P s) s)).toReal) r  := by
  have ae_eventually_mem_cylinder_iff :
      ∀ᵐ Y ∂volume, ∀ᶠ s in 𝓝 r,
      Y ∈ backwardCylinder (P s) s ↔ Y ∈ backwardCylinder (P r) r := by
    have hvface : volume {Y : KineticPoint d |
        PDE.vecNormSq (Y.velocity-(P r).velocity) = r^2} = 0 :=
      volume_velocity_sphere_face (P r).velocity hr
    have hpface : volume {Y : KineticPoint d |
        PDE.vecNormSq (relativePosition (P r) Y) = (r^3)^2} = 0 := by
      simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using
        volume_position_sphere_face (P r) (pow_pos hr 3)
    filter_upwards [ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time)
        ((P r).time-r^2) (volume_time_face _),
      ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time) (P r).time (volume_time_face _),
      ae_ne_of_null_fiber _ _ hvface, ae_ne_of_null_fiber _ _ hpface] with Y ht₁ ht₂ hv hp
    have ht : Continuous (fun s => (P s).time) := continuous_time.comp hP
    have hx : Continuous (fun s => (P s).position) := continuous_position.comp hP
    have hvp : Continuous (fun s => (P s).velocity) := continuous_velocity.comp hP
    have hrel : Continuous (fun s => relativePosition (P s) Y) :=
      (continuous_const.sub hx).sub ((continuous_const.sub ht).smul hvp)
    have e₁ := eventually_lt_iff_of_ne (ht.sub (continuous_id.pow 2)).continuousAt
      continuous_const.continuousAt ht₁.symm
    have e₂ := eventually_lt_iff_of_ne continuous_const.continuousAt ht.continuousAt ht₂
    have e₃ := eventually_lt_iff_of_ne
      (PDE.continuous_vecNormSq.comp (continuous_const.sub hvp)).continuousAt
      (continuous_id.pow 2).continuousAt hv
    have e₄ := eventually_lt_iff_of_ne (PDE.continuous_vecNormSq.comp hrel).continuousAt
      ((continuous_id.pow 3).pow 2).continuousAt hp
    filter_upwards [e₁, e₂, e₃, e₄] with s h₁ h₂ h₃ h₄
    simpa only [backwardCylinder, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq,
      sub_zero, Pi.sub_apply, Pi.pow_apply, Function.comp_apply, id_eq] using
        and_congr h₁ (and_congr h₂ (and_congr h₃ h₄))
  change Tendsto _ (𝓝 r) (𝓝 _)
  let : IsFiniteMeasure (volume.restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE.lt_top⟩
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 r)
    (μ := volume.restrict E) (isOpen_cylinder (P r) r).measurableSet
    (fun s => (isOpen_cylinder (P s) s).measurableSet)
    (ae_restrict_of_ae (ae_eventually_mem_cylinder_iff))
  have hreal := (ENNReal.continuousAt_toReal (measure_ne_top
    (volume.restrict E) (backwardCylinder (P r) r))).tendsto.comp hlim
  simpa only [Measure.restrict_apply (isOpen_cylinder _ _).measurableSet, inter_comm,
    Function.comp_def]
    using hreal




/-- Near-full density on a finite superset transfers after accounting for its volume ratio. -/
theorem density_transfer_subset {d : ℕ} {E A B : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hAB : A ⊆ B) (hB : volume B ≠ ⊤)
    {eta k : ℝ} (hk : 0 < k)
    (hvol : (volume B).toReal = k*(volume A).toReal)
    (hdensity : (1-eta/k)*(volume B).toReal ≤ (volume (E ∩ B)).toReal) :
    (1-eta)*(volume A).toReal ≤ (volume (E ∩ A)).toReal := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono hAB)
  have hDA : volume (A \ E) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono sdiff_subset)
  have hDB : volume (B \ E) ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono sdiff_subset)
  have hIA : volume (A ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono inter_subset_left)
  have hIB : volume (B ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono inter_subset_left)
  have ha := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) A hE)
  have hb := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) B hE)
  rw [ENNReal.toReal_add hIA hDA, inter_comm A E] at ha
  rw [ENNReal.toReal_add hIB hDB, inter_comm B E] at hb
  have hd := ENNReal.toReal_mono hDB (measure_mono (sdiff_subset_sdiff_left hAB))
  have heq : (eta/k)*(volume B).toReal = eta*(volume A).toReal := by
    rw [hvol]
    field_simp
  nlinarith only [ha, hb, hd, hdensity, heq]






/-- Almost every point away from the spatial shell has an admissible critical cylinder. -/
theorem ae_exists_critical_cylinder {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    ∀ᵐ X ∂(volume.restrict E), PDE.vecEuclideanNorm X.position < 1-2*R^2 →
      ∃ P r, 0 < r ∧ r < R ∧ X ∈ backwardCylinder P r ∧
        backwardCylinder P r ⊆ unitCylinder d ∧
        (volume (E ∩ backwardCylinder P r)).toReal =
          (1-eta)*(volume (backwardCylinder P r)).toReal    := by
  let saturationGap {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) (X : KineticPoint d) (r : ℝ) :=
    (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal-
        (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal
  have continuousAt_saturationGap {d : ℕ} {E : Set (KineticPoint d)} (hE : volume E ≠ ⊤) (X : KineticPoint d) {r : ℝ} (hr : 0 < r) :
      ContinuousAt (saturationGap E eta X) r := by
    have continuous_saturationCenter :
        Continuous (saturationCenter X) := by
      apply KineticPoint.continuous_mk <;> fun_prop
    have hV : ContinuousAt
        (fun s : ℝ => (volume (backwardCylinder (saturationCenter X s) s)).toReal) r := by
      have heq : (fun s : ℝ => (volume (backwardCylinder (saturationCenter X s) s)).toReal)
          =ᶠ[𝓝 r] (fun s => s^(4*d+2)*(volume (unitCylinder d)).toReal) := by
        filter_upwards [eventually_gt_nhds hr] with s hs
        rw [volume_cylinder_eq_unit _ hs, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity)]
        rfl
      apply ContinuousAt.congr_of_eventuallyEq ?_ heq
      fun_prop
    exact (continuousAt_cylinder_inter_volume (saturationCenter X)
      (continuous_saturationCenter) hE hr).sub (continuousAt_const.mul hV)
  have ae_saturationCylinder_density :
      ∀ᵐ X ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
      ∃ r1 : ℝ, 0 < r1 ∧ ∀ r : ℝ, 0 < r → r < r1 →
        (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal ≤
          (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal := by
    filter_upwards [ae_centeredCylinder_density_all hE hbounded, ae_restrict_mem₀ hE]
      with X hX hXE
    intro eta heta
    let k : ℝ := 2^(4*d+2)
    have hk : 0 < k := by positivity
    obtain ⟨s, hs, hsmall⟩ := hX (eta/k) (div_pos heta hk)
    refine ⟨s/2, half_pos hs, ?_⟩
    intro r hr hrr
    apply density_transfer_subset hE (saturationCylinder_subset_centered (hEQ hXE) hr)
      (volume_cylinder_pos_ne_top (centeredTop X (2*r)) (by positivity)).2 hk
    · unfold centeredCylinder
      rw [volume_cylinder_eq_unit _ (by positivity : 0 < 2*r),
        volume_cylinder_eq_unit _ hr, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*r)^(4*d+2)),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ r^(4*d+2)), mul_pow]
      ring
    · exact hsmall (2*r) (by positivity) (by linarith)
  filter_upwards [ae_saturationCylinder_density, ae_restrict_mem₀ hE]
    with X hd hXE
  intro hx
  obtain ⟨s, hs, hsmall⟩ := hd (eta/2) (half_pos heta)
  let a := min s R/2
  have ha : 0 < a := half_pos (lt_min hs hR)
  have has : a < s := (half_lt_self (lt_min hs hR)).trans_le (min_le_left _ _)
  have haR : a < R := (half_lt_self (lt_min hs hR)).trans_le (min_le_right _ _)
  have hpos : 0 < saturationGap E eta X a := by
    have hdense := hsmall a ha has
    have hvol := ENNReal.toReal_pos
      (volume_cylinder_pos_ne_top (saturationCenter X a) ha).1.ne'
      (volume_cylinder_pos_ne_top (saturationCenter X a) ha).2
    dsimp [saturationGap]
    nlinarith
  have hneg : saturationGap E eta X R < 0 := by
    by_contra hn
    have hdense : (1-eta)*(volume (backwardCylinder (saturationCenter X R) R)).toReal ≤
        (volume (E ∩ backwardCylinder (saturationCenter X R) R)).toReal := by
      change ¬ _ < 0 at hn
      dsimp [saturationGap] at hn
      linarith
    have h := hcutoff (saturationCenter X R) R hR
      (saturationCylinder_subset_unit (hEQ hXE) hR le_rfl hR1 hx) hdense
    exact (lt_irrefl R) h
  have hc : ContinuousOn (saturationGap E eta X) (Icc a R) := by
    intro r hr
    exact (continuousAt_saturationGap (volume_bounded_ne_top hbounded) X
      (ha.trans_le hr.1)).continuousWithinAt
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' haR.le hc ⟨hneg.le, hpos.le⟩
  have hrpos : 0 < r := ha.trans_le hr.1
  have hrR : r < R := lt_of_le_of_ne hr.2 (by
    intro he
    rw [he] at heq
    linarith)
  refine ⟨saturationCenter X r, r, hrpos, hrR,
    self_mem_saturationCylinder (hEQ hXE) hrpos,
    saturationCylinder_subset_unit (hEQ hXE) hrpos hrR.le hR1 hx, ?_⟩
  dsimp [saturationGap] at heq
  linarith



/-- A uniformly sub-full cylinder family leaves a definite fraction of its union outside E. -/
theorem cylinder_union_density_defect {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (E : Set (KineticPoint d)) (hE : NullMeasurableSet E volume)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hdensity : ∀ i ∈ t, (volume (E ∩ backwardCylinder (P i) (r i))).toReal ≤
      (1-eta)*(volume (backwardCylinder (P i) (r i))).toReal) :
    ENNReal.ofReal eta * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal ((8 : ℝ)^(4*d+2)) *
        volume ((⋃ i ∈ t, backwardCylinder (P i) (r i)) \ E) := by
  let H := ⋃ i ∈ t, backwardCylinder (P i) (r i)
  apply cylinder_family_weak_type P r t R hr hR (H \ E) (ENNReal.ofReal eta)
  intro i hi
  have hsub : backwardCylinder (P i) (r i) ⊆ H := subset_iUnion₂_of_subset i hi subset_rfl
  have heq : (H \ E) ∩ backwardCylinder (P i) (r i) =
      backwardCylinder (P i) (r i) \ E := by
    ext X
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  rw [heq]
  exact measure_density_defect hE (volume_cylinder_pos_ne_top (P i) (hr i hi)).2
    heta (hdensity i hi)

/-- Real-valued form of the strict density reduction inside a finite critical union. -/
theorem cylinder_union_density_reduction {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (E : Set (KineticPoint d)) (hE : NullMeasurableSet E volume)
    (hfinite : volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≠ ⊤)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hdensity : ∀ i ∈ t, (volume (E ∩ backwardCylinder (P i) (r i))).toReal ≤
      (1-eta)*(volume (backwardCylinder (P i) (r i))).toReal) :
    (volume (E ∩ (⋃ i ∈ t, backwardCylinder (P i) (r i)))).toReal ≤
      (1-eta/((8 : ℝ)^(4*d+2))) *
        (volume (⋃ i ∈ t, backwardCylinder (P i) (r i))).toReal := by
  let H := ⋃ i ∈ t, backwardCylinder (P i) (r i)
  have hD : volume (H \ E) ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  have hI : volume (H ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (measure_mono inter_subset_left)
  have hineq := cylinder_union_density_defect P r t R hr hR E hE heta hdensity
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD) hineq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal heta,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (8 : ℝ)^(4*d+2))] at hreal
  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) H hE)
  rw [ENNReal.toReal_add hI hD, inter_comm H E] at hsum
  have hB : 0 < (8 : ℝ)^(4*d+2) := by positivity
  have hdiv : eta*(volume H).toReal/((8 : ℝ)^(4*d+2)) ≤ (volume (H \ E)).toReal :=
    (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hreal)
  rw [mul_div_right_comm] at hdiv
  nlinarith only [hsum, hdiv]



/-- Critical cylinders have exactly the prescribed density and lie inside Q. -/
def criticalParameters {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) :
    Set (KineticPoint d × ℝ) :=
  {z | 0 < z.2 ∧ backwardCylinder z.1 z.2 ⊆ unitCylinder d ∧
    (volume (E ∩ backwardCylinder z.1 z.2)).toReal =
      (1-eta)*(volume (backwardCylinder z.1 z.2)).toReal}

/-- The open union of all critical cylinders. -/
def criticalUnion {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  ⋃ z ∈ criticalParameters E eta, backwardCylinder z.1 z.2




/-- Outside the critical union, E costs only the spatial boundary layer. -/
theorem volume_outside_criticalUnion_le {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta)
    (hR : 0 < R) (hRsmall : R ≤ 1/4)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    (volume (E \ criticalUnion E eta)).toReal ≤
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
  have hc := ae_exists_critical_cylinder hE hbounded hEQ heta hR
    (hRsmall.trans (by norm_num : (1 : ℝ)/4 ≤ 1)) hcutoff
  have hae := (ae_restrict_iff'₀ hE).mp hc
  have hsub : (E \ criticalUnion E eta) ≤ᵐ[volume] (unitCylinder d \ spatialCore d R) := by
    filter_upwards [hae] with X hX
    intro hEX
    refine ⟨hEQ hEX.1, ?_⟩
    intro hcore
    have hx : PDE.vecEuclideanNorm X.position < 1-2*R^2 := by
      have h := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by nlinarith : 0 < 1-2*R^2)).mp hcore.2.2.1
      simpa only [sub_zero] using h
    obtain ⟨P, r, hr, _, hmem, hPQ, heq⟩ := hX hEX.1 hx
    apply hEX.2
    exact mem_iUnion₂.mpr ⟨(P,r), ⟨hr, hPQ, heq⟩, hmem⟩
  have hf : volume (unitCylinder d \ spatialCore d R) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono sdiff_subset)
  exact (ENNReal.toReal_mono hf (measure_mono_ae hsub)).trans
    (spatial_shell_volume d hR hRsmall)

/-- Exact-density cylinders yield a fixed proportional density reduction in their union. -/
theorem criticalUnion_density_reduction {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) {eta R : ℝ} (heta : 0 ≤ eta)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    (volume (E ∩ criticalUnion E eta)).toReal ≤
      (1-eta/((8 : ℝ)^(4*d+2)))*(volume (criticalUnion E eta)).toReal  := by
  have criticalUnion_subset_unit :
      criticalUnion E eta ⊆ unitCylinder d := by
    intro X hX
    obtain ⟨z, hz, hmem⟩ := mem_iUnion₂.mp hX
    exact hz.2.1 hmem
  have hf : volume (criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono (criticalUnion_subset_unit))
  exact cylinder_union_density_reduction Prod.fst Prod.snd (criticalParameters E eta) R
    (fun _ hz => hz.1)
    (fun z hz => (hcutoff z.1 z.2 hz.1 hz.2.1 (le_of_eq hz.2.2.symm)).le)
    E hE hf heta (fun _ hz => hz.2.2.le)



/-- The critical union is controlled by F inside Q and a linear small-height leakage error. -/
theorem criticalUnion_delay_bound {d : ℕ} {E F : Set (KineticPoint d)}
    {eta R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (m : ℕ) (hm : 0 < m)
    (hheight : (m : ℝ)*R^2 ≤ 1)
    (hstack : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F) :
    (volume (criticalUnion E eta)).toReal ≤
      (((m : ℝ)+1)/(m : ℝ))*((volume (F ∩ unitCylinder d)).toReal+
        2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2))    := by
  have volume_roundBox_ne_top (a : ℝ) (b : ℝ) {R : ℝ} (hR : 0 < R) :
      volume (roundBox d a b R) ≠ ⊤ := by
    rw [volume_roundBox d a b hR]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (volume_cylinder_pos_ne_top _ zero_lt_one).2
  have leakage_shell_volume {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
      (volume (roundBox d (-1) h (1+4*h) \ unitCylinder d)).toReal ≤
      2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*h := by
    have unit_subset_leakage_envelope :
        unitCylinder d ⊆ roundBox d (-1) h (1+4*h) := by
      intro X hX
      obtain ⟨htlo, hthi, hv, hx⟩ := (mem_unitCylinder_iff X).mp hX
      refine ⟨htlo, hthi.trans h0, ?_, ?_⟩
      · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]
        linarith
      · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
        exact hv
    have hQ : NullMeasurableSet (unitCylinder d) volume :=
      (isOpen_cylinder _ _).measurableSet.nullMeasurableSet
    rw [volume_sdiff_toReal_of_subset hQ
      (unit_subset_leakage_envelope)
      (volume_roundBox_ne_top (-1) h (by positivity))]
    have hb := leakage_envelope_volume (d := d) h0 h1
    linarith
  have exists_countable_critical_subcover :
      ∃ T ⊆ criticalParameters E eta, T.Countable ∧
      (⋃ z ∈ T, backwardCylinder z.1 z.2) = criticalUnion E eta := by
    let : SecondCountableTopology (KineticPoint d) :=
      (KineticPoint.homeomorphProd d).secondCountableTopology
    exact TopologicalSpace.isOpen_biUnion_countable (criticalParameters E eta)
      (fun z => backwardCylinder z.1 z.2) (fun z _ => isOpen_cylinder z.1 z.2)
  obtain ⟨T, hT, hTc, hcover⟩ := exists_countable_critical_subcover
  let : Countable T := hTc.to_subtype
  let P : T → KineticPoint d := fun z => z.1.1
  let r : T → ℝ := fun z => z.1.2
  have hz (z : T) : 0 < r z ∧ backwardCylinder (P z) (r z) ⊆ unitCylinder d ∧
      (volume (E ∩ backwardCylinder (P z) (r z))).toReal =
        (1-eta)*(volume (backwardCylinder (P z) (r z))).toReal := hT z.2
  have hs (z : T) : r z < R ∧ forwardStack (P z) (r z) m ⊆ F :=
    hstack (P z) (r z) (hz z).1 (hz z).2.1 (hz z).2.2.symm.le
  let J := ⋃ z : T, openForwardStack (P z) (r z) m
  have hJopen : IsOpen J := isOpen_iUnion fun z => isOpen_openForwardStack (P z) (r z) m
  have hJF : J ⊆ F := by
    intro X hX
    obtain ⟨z, hz⟩ := mem_iUnion.mp hX
    exact (hs z).2 hz.1
  have hJbox : J ⊆ roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2) := by
    intro X hX
    obtain ⟨z, hmem⟩ := mem_iUnion.mp hX
    exact forwardStack_subset_roundBox (hz z).1 (hs z).1 hR1 (hz z).2.1 m hm hmem.1
  have hheight0 : 0 < (m : ℝ)*R^2 := mul_pos (by exact_mod_cast hm) (sq_pos_of_pos hR)
  have hboxfinite := volume_roundBox_ne_top (-1) ((m : ℝ)*R^2)
    (by positivity : 0 < 1+4*(m : ℝ)*R^2)
  have hJfinite : volume J ≠ ⊤ := ne_top_of_le_ne_top hboxfinite (measure_mono hJbox)
  have hFQfinite : volume (F ∩ unitCylinder d) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono inter_subset_right)
  have hDfinite : volume (roundBox d (-1) ((m : ℝ)*R^2)
      (1+4*(m : ℝ)*R^2) \ unitCylinder d) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxfinite (measure_mono sdiff_subset)
  have hJbound : (volume J).toReal ≤ (volume (F ∩ unitCylinder d)).toReal+
      2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2) := by
    have hsub : J ⊆ (F ∩ unitCylinder d) ∪
        (roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2) \ unitCylinder d) := by
      intro X hX
      by_cases hQ : X ∈ unitCylinder d
      · exact Or.inl ⟨hJF hX, hQ⟩
      · exact Or.inr ⟨hJbox hX, hQ⟩
    have hb := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hFQfinite, hDfinite⟩) hb
    rw [ENNReal.toReal_add hFQfinite hDfinite] at hreal
    have hshell : (volume (roundBox d (-1) ((m : ℝ)*R^2)
        (1+4*(m : ℝ)*R^2) \ unitCylinder d)).toReal ≤
        2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2) := by
      simpa only [mul_assoc] using leakage_shell_volume hheight0 hheight
    linarith only [hreal, hshell]
  have hH : (⋃ z : T, backwardCylinder (P z) (r z)) = criticalUnion E eta := by
    rw [iUnion_subtype]
    exact hcover
  have hdelay := delayed_union_countable P r (fun z => (hz z).1) m hm
  rw [hH] at hdelay
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfinite) hdelay
  have hq : 0 ≤ ((m : ℝ)+1)/(m : ℝ) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left hJbound hq)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots
open Set MeasureTheory Covering


/-- Proportional gain from factor-eight kinetic selection. -/
def coveringGain (d : ℕ) : ℝ := ((8 : ℝ)^(4*d+2))⁻¹

/-- A single dimension-only constant absorbs both spatial and delayed leakage shells. -/
def coveringLeakage (d : ℕ) : ℝ :=
  (32+4*(5 : ℝ)^d+4*(d : ℝ))*(volume (unitCylinder d)).toReal

/-- The gain is positive and no larger than one half. -/
theorem coveringGain_bounds (d : ℕ) : 0 < coveringGain d ∧ coveringGain d ≤ 1/2 := by
  have hB : 2 ≤ (8 : ℝ)^(4*d+2) := by
    rw [pow_add]
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) (n := 4*d)
    norm_num
    nlinarith
  have hpos : 0 < coveringGain d := inv_pos.mpr (by positivity)
  have heq : coveringGain d*(8 : ℝ)^(4*d+2) = 1 := inv_mul_cancel₀ (by positivity)
  exact ⟨hpos, by nlinarith⟩


/-- The delayed multiplier is at least one for every positive natural height. -/
theorem delay_multiplier_ge_one {m : ℕ} (hm : 0 < m) :
    1 ≤ ((m : ℝ)+1)/(m : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
  linarith

/-- A positive threshold leaves at least half of the multiplicative density factor. -/
theorem density_factor_bounds (d : ℕ) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    1/2 ≤ 1-coveringGain d*eta ∧ 1-coveringGain d*eta ≤ 1 := by
  obtain ⟨hc, hc1⟩ := coveringGain_bounds d
  constructor <;> nlinarith

/-- The two small-height errors fit inside the chosen final leakage constant. -/
theorem absorb_covering_errors {e f V k n a q h s : ℝ}
    (hV : 0 ≤ V) (hk : 0 ≤ k) (hn : 0 ≤ n) (ha : 1/2 ≤ a) (hq : 1 ≤ q)
    (hh : 0 ≤ h) (hs : s ≤ h)
    (he : e ≤ a*q*(f+2*k*V*h)+2*n*V*s) :
    e ≤ q*a*(f+(32+4*k+4*n)*V*h) := by
  have hqa : 1/2 ≤ q*a := by nlinarith
  have hcoef : 0 ≤ (32+4*k+4*n)*V-2*k*V := by nlinarith
  have hcoeff : 2*n*V ≤ (1/2)*((32+4*k+4*n)*V-2*k*V) := by nlinarith
  have herr : 2*n*V*s ≤ q*a*(((32+4*k+4*n)*V-2*k*V)*h) := by
    calc
      _ ≤ 2*n*V*h := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (1/2)*(((32+4*k+4*n)*V-2*k*V)*h) := by
        nlinarith only [mul_le_mul_of_nonneg_right hcoeff hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right hqa (mul_nonneg hcoef hh)
  nlinarith only [he, herr]

/-- When the error height is at least 1/16 the desired upper bound is already unit volume. -/
theorem trivial_large_height {V f C q a h : ℝ} (hV : 0 ≤ V) (hf : 0 ≤ f)
    (hC : 32*V ≤ C) (hq : 1 ≤ q) (ha : 1/2 ≤ a) (hh : 1/16 ≤ h) :
    V ≤ q*a*(f+C*h) := by
  have hqa : 1/2 ≤ q*a := by nlinarith
  have hC0 : 0 ≤ C := by linarith
  have hCh : 2*V ≤ C*h := by
    have h := mul_le_mul_of_nonneg_left hh hC0
    nlinarith
  have hnon : 0 ≤ f+C*h := by nlinarith
  have h := mul_le_mul_of_nonneg_right hqa hnon
  nlinarith



/-- Small-cutoff ink spots follow from critical density, delayed unions and the two shells. -/
theorem ink_spots_small_cutoff {d : ℕ} {E F : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta) (heta1 : eta < 1)
    (hR : 0 < R) (hRsmall : R ≤ 1/4) (m : ℕ) (hm : 0 < m)
    (hheight : (m : ℝ)*R^2 ≤ 1)
    (hstack : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F) :
    (volume E).toReal ≤ (((m : ℝ)+1)/(m : ℝ))*(1-coveringGain d*eta)*
      ((volume (F ∩ unitCylinder d)).toReal+coveringLeakage d*(m : ℝ)*R^2)  := by
  have isOpen_criticalUnion : IsOpen (criticalUnion E eta) :=
    isOpen_biUnion fun z _ => isOpen_cylinder z.1 z.2
  have hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R :=
    fun P r hr hsub hd => (hstack P r hr hsub hd).1
  have hout := volume_outside_criticalUnion_le hE hbounded hEQ heta hR hRsmall hcutoff
  have hred := criticalUnion_density_reduction hE heta.le hcutoff
  have hdelay := criticalUnion_delay_bound hR (hRsmall.trans (by norm_num)) m hm hheight hstack
  have hEfinite : volume E ≠ ⊤ := volume_bounded_ne_top hbounded
  have hIfinite : volume (E ∩ criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top hEfinite (measure_mono inter_subset_left)
  have hDfinite : volume (E \ criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top hEfinite (measure_mono sdiff_subset)
  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) E
    (isOpen_criticalUnion).measurableSet.nullMeasurableSet)
  rw [ENNReal.toReal_add hIfinite hDfinite] at hsum
  have he : (volume E).toReal ≤ (1-coveringGain d*eta)*(volume (criticalUnion E eta)).toReal+
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
    have heq : eta/(8 : ℝ)^(4*d+2) = coveringGain d*eta := by
      rw [coveringGain, div_eq_mul_inv, mul_comm]
    rw [heq] at hred
    linarith only [hsum, hred, hout]
  have ha := density_factor_bounds d heta heta1
  have hq := delay_multiplier_ge_one hm
  have hdelay' := mul_le_mul_of_nonneg_left hdelay
    (by linarith only [ha.1] : 0 ≤ 1-coveringGain d*eta)
  have he' : (volume E).toReal ≤
      (1-coveringGain d*eta)*(((m : ℝ)+1)/(m : ℝ))*
        ((volume (F ∩ unitCylinder d)).toReal+
          2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2))+
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
    nlinarith only [he, hdelay']
  have hs : R^2 ≤ (m : ℝ)*R^2 := by
    have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [sq_nonneg R]
  have hb := absorb_covering_errors
    (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
    (by positivity : 0 ≤ (5 : ℝ)^d) (Nat.cast_nonneg d) ha.1 hq
    (by positivity : 0 ≤ (m : ℝ)*R^2) hs he'
  simpa only [coveringLeakage, mul_assoc] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory Covering InkSpots

/-- Kinetic crawling ink spots with dimension-only constants and the leakage error. -/
theorem kinetic_crawling_ink_spots_aux (d : ℕ) (_hd : 1 ≤ d) :
    ∃ c_d C_d : ℝ, 0 < c_d ∧ c_d < 1 ∧ 0 < C_d ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (eta r₀ : ℝ), 0 < eta → eta < 1 → 0 < r₀ → r₀ < 1 →
      ∀ (E F : Set (KineticPoint d)),
        Bornology.IsBounded E → Bornology.IsBounded F →
        NullMeasurableSet E volume → NullMeasurableSet F volume →
        E ⊆ F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
        (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
          backwardCylinder P r ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
          (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
            (volume (E ∩ backwardCylinder P r)).toReal →
          r < r₀ ∧ forwardStack P r m ⊆ F) →
        (volume E).toReal ≤
          (((m : ℝ) + 1) / (m : ℝ)) * (1 - c_d * eta) *
            ((volume (F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal +
              C_d * (m : ℝ) * r₀ ^ 2)  := by
  have coveringLeakage_bounds :
      0 < coveringLeakage d ∧
    32*(volume (unitCylinder d)).toReal ≤ coveringLeakage d := by
    have hV : 0 < (volume (unitCylinder d)).toReal := ENNReal.toReal_pos
      (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
      (volume_cylinder_pos_ne_top _ zero_lt_one).2
    have hn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hk : 0 ≤ (5 : ℝ)^d := by positivity
    dsimp [coveringLeakage]
    constructor <;> nlinarith
  obtain ⟨hc, hc1⟩ := coveringGain_bounds d
  obtain ⟨hC, hCV⟩ := coveringLeakage_bounds
  refine ⟨coveringGain d, coveringLeakage d, hc, by linarith, hC, ?_⟩
  intro m hm eta R heta heta1 hR hR1 E F hEb _hFb hE _hF hEF hstack
  have hEQ : E ⊆ unitCylinder d := fun X hX => (hEF hX).2
  have hs : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F := hstack
  by_cases hsmall : R ≤ 1/4
  · by_cases hheight : (m : ℝ)*R^2 ≤ 1
    · exact ink_spots_small_cutoff hE hEb hEQ heta heta1 hR hsmall m hm hheight hs
    · have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by linarith only [hheight]
      have hbound := trivial_large_height
        (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
        (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
        (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
      have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
        (measure_mono hEQ)
      exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)
  · have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by nlinarith
    have hbound := trivial_large_height
      (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
      (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
      (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
    have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono hEQ)
    exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

end

