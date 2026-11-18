module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.MetricSpace.ProperSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
open Set MeasureTheory
open scoped Topology


/-- The top of a time-centered cylinder based at P. -/
def centeredTop {d : ℕ} (P : KineticPoint d) (r : ℝ) : KineticPoint d :=
  ⟨P.time + r ^ 2 / 2, P.position + (r ^ 2 / 2) • P.velocity, P.velocity⟩

/-- The literal time-centered cylinder used for differentiation. -/
def centeredCylinder {d : ℕ} (P : KineticPoint d) (r : ℝ) : Set (KineticPoint d) :=
  backwardCylinder (centeredTop P r) r

/-- Centering preserves the free-transport position coordinate. -/
theorem relativePosition_centeredTop {d : ℕ} (P X : KineticPoint d) (r : ℝ) :
    relativePosition (centeredTop P r) X = relativePosition P X := by
  ext i
  simp only [relativePosition, centeredTop, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Membership in the centered basis is stated in its physical Euclidean coordinates. -/
theorem mem_centeredCylinder_iff {d : ℕ} (P X : KineticPoint d) {r : ℝ}
    (hr : 0 < r) :
    X ∈ centeredCylinder P r ↔
      |X.time-P.time| < r ^ 2 / 2 ∧
      PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
      PDE.vecEuclideanNorm (relativePosition P X) < r ^ 3 := by
  rw [centeredCylinder, mem_backwardCylinder_iff,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3),
    relativePosition_centeredTop, sub_zero]
  simp only [centeredTop, abs_lt]
  constructor
  · rintro ⟨h1, h2, hv, hx⟩
    exact ⟨⟨by linarith only [h1], by linarith only [h2]⟩, hv, hx⟩
  · rintro ⟨⟨h1, h2⟩, hv, hx⟩
    exact ⟨by linarith only [h1], by linarith only [h2], hv, hx⟩

/-- The distinguished point belongs to each positive centered cylinder. -/
theorem self_mem_centeredCylinder {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) : P ∈ centeredCylinder P r := by
  rw [mem_centeredCylinder_iff P P hr]
  have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
    PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
  simp only [sub_self, abs_zero, relativePosition_self, hz]
  exact ⟨half_pos (sq_pos_of_pos hr), hr, pow_pos hr 3⟩

/-- Relative position plus transport displacement is the physical position difference. -/
theorem position_sub_eq_relative {d : ℕ} (P X : KineticPoint d) :
    X.position-P.position = relativePosition P X + (X.time-P.time) • P.velocity := by
  simp only [relativePosition, sub_add_cancel]









/-- Every bounded kinetic set has finite volume. -/
theorem volume_bounded_ne_top {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : volume E ≠ ⊤   := by
  have locallyFinite_kinetic_volume :
      IsLocallyFiniteMeasure (volume : Measure (KineticPoint d)) := by
    refine ⟨fun P => ?_⟩
    refine ⟨centeredCylinder P 1,
      (isOpen_cylinder (centeredTop P 1) 1).mem_nhds (self_mem_centeredCylinder P zero_lt_one),
      ?_⟩
    exact lt_top_iff_ne_top.mpr (volume_cylinder_pos_ne_top (centeredTop P 1) zero_lt_one).2
  have properSpace_kineticPoint :
      ProperSpace (KineticPoint d) := by
    refine ⟨fun P R => ?_⟩
    have h := (isCompact_closedBall ((KineticPoint.isometryEquivProd d) P) R).image
      (KineticPoint.isometryEquivProd d).symm.continuous
    rw [(KineticPoint.isometryEquivProd d).symm.image_closedBall,
      (KineticPoint.isometryEquivProd d).symm_apply_apply] at h
    exact h
  let : ProperSpace (KineticPoint d) := properSpace_kineticPoint
  let : IsLocallyFiniteMeasure (volume : Measure (KineticPoint d)) :=
    locallyFinite_kinetic_volume
  exact hE.measure_lt_top.ne



/-- Points of E with arbitrarily small failures of a fixed near-full density threshold. -/
def densityFailure {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  {P | P ∈ E ∧ ∀ r0 : ℝ, 0 < r0 → ∃ r : ℝ, 0 < r ∧ r < r0 ∧
    (volume (E ∩ centeredCylinder P r)).toReal <
      (1-eta)*(volume (centeredCylinder P r)).toReal}



/-- Null-measurable finite-volume sets satisfy the same density theorem. -/
theorem volume_densityFailure_eq_zero {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hfinite : volume E ≠ ⊤)
    {eta : ℝ} (heta : 0 < eta) : volume (densityFailure E eta) = 0   := by
  have centeredCylinder_eventually_subset_open {U : Set (KineticPoint d)} (hU : IsOpen U) {P : KineticPoint d} (hP : P ∈ U) :
      ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 → centeredCylinder P r ⊆ U := by
    have centeredCylinder_subset_ball {eps : ℝ} (heps : 0 < eps) :
        ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
        centeredCylinder P r ⊆ Metric.ball P eps := by
      have centeredCylinder_coordinate_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {X : KineticPoint d} (hX : X ∈ centeredCylinder P r) :
          |X.time-P.time| < r ∧
          PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
          PDE.vecEuclideanNorm (X.position-P.position) <
            r*(1+PDE.vecEuclideanNorm P.velocity) := by
        obtain ⟨ht, hv, hx⟩ := (mem_centeredCylinder_iff P X hr).mp hX
        have hr2 : r ^ 2 ≤ r := by nlinarith only [hr, hr1]
        have hr3 : r ^ 3 ≤ r := by
          calc
            r ^ 3 = r ^ 2 * r := by ring
            _ ≤ r * r := mul_le_mul_of_nonneg_right hr2 hr.le
            _ ≤ r := by nlinarith only [hr, hr1]
        have ht' : |X.time-P.time| < r := by linarith only [ht, hr2, hr]
        refine ⟨ht', hv, ?_⟩
        rw [position_sub_eq_relative]
        calc
          _ ≤ PDE.vecEuclideanNorm (relativePosition P X) +
              PDE.vecEuclideanNorm ((X.time-P.time) • P.velocity) :=
            PDE.vecEuclideanNorm_add_le _ _
          _ = PDE.vecEuclideanNorm (relativePosition P X) +
              |X.time-P.time| *PDE.vecEuclideanNorm P.velocity := by
            rw [PDE.vecEuclideanNorm_smul]
          _ < r + r*PDE.vecEuclideanNorm P.velocity :=
            add_lt_add_of_lt_of_le (hx.trans_le hr3)
              (mul_le_mul_of_nonneg_right ht'.le (PDE.vecEuclideanNorm_nonneg _))
          _ = r*(1+PDE.vecEuclideanNorm P.velocity) := by ring
      let L := 1 + PDE.vecEuclideanNorm P.velocity
      have hL : 0 < L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
      have hL1 : 1 ≤ L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
      refine ⟨min 1 (eps/L), lt_min zero_lt_one (div_pos heps hL), ?_⟩
      intro r hr hrr X hX
      have hr1 : r ≤ 1 := (hrr.trans_le (min_le_left _ _)).le
      have hrL : r*L < eps := (lt_div_iff₀ hL).mp (hrr.trans_le (min_le_right _ _))
      obtain ⟨ht, hv, hx⟩ := centeredCylinder_coordinate_bounds hr hr1 hX
      have hrle : r ≤ r*L := by nlinarith only [hr.le, hL1]
      have hpos : dist X.position P.position < eps := by
        rw [dist_eq_norm]
        exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hx.trans hrL)
      have hvel : dist X.velocity P.velocity < eps := by
        rw [dist_eq_norm]
        exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hv.trans_le hrle |>.trans hrL)
      rw [Metric.mem_ball, ← (KineticPoint.isometryEquivProd d).dist_eq]
      change max (dist X.time P.time)
        (max (dist X.position P.position) (dist X.velocity P.velocity)) < eps
      rw [max_lt_iff, max_lt_iff, Real.dist_eq]
      exact ⟨ht.trans_le hrle |>.trans hrL, hpos, hvel⟩
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU P hP
    obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_subset_ball heps
    exact ⟨r0, hr0, fun r hr hrr => (hsmall r hr hrr).trans hball⟩
  have volume_densityFailure_eq_zero_of_measurable {E : Set (KineticPoint d)} (hE : MeasurableSet E) (hfinite : volume E ≠ ⊤) :
      volume (densityFailure E eta) = 0 := by
    have densityFailure_subset_error_maximal {E : Set (KineticPoint d)} {U : Set (KineticPoint d)} (hE : NullMeasurableSet E volume) (hU : IsOpen U) (hEU : E ⊆ U) :
        densityFailure E eta ⊆ maximalCylinderUnion (U \ E) (ENNReal.ofReal eta) := by
      intro P hP
      obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_eventually_subset_open hU (hEU hP.1)
      obtain ⟨r, hr, hrr, hdef⟩ := hP.2 (min r0 1) (lt_min hr0 zero_lt_one)
      have hsub := hsmall r hr (hrr.trans_le (min_le_left _ _))
      have heq : (U \ E) ∩ centeredCylinder P r = centeredCylinder P r \ E := by
        ext X
        constructor
        · exact fun h => ⟨h.2, h.1.2⟩
        · exact fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩
      have hcharge := measure_density_defect hE
        (volume_cylinder_pos_ne_top (centeredTop P r) hr).2 heta.le hdef.le
      change ENNReal.ofReal eta * volume (centeredCylinder P r) ≤
        volume (centeredCylinder P r \ E) at hcharge
      rw [← heq] at hcharge
      exact mem_iUnion₂.mpr ⟨(centeredTop P r, r),
        ⟨hr, (hrr.trans_le (min_le_right _ _)).le, hcharge⟩,
        self_mem_centeredCylinder P hr⟩
    have outerRegular_kinetic_volume :
        Measure.OuterRegular (volume : Measure (KineticPoint d)) := by
      change Measure.OuterRegular
        (Measure.map (KineticPoint.homeomorphProd d).symm
          (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))))
      let : Measure.Regular (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))) :=
        Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure volume
      exact Measure.OuterRegular.map (KineticPoint.homeomorphProd d).symm volume
    let : Measure.OuterRegular (volume : Measure (KineticPoint d)) :=
      outerRegular_kinetic_volume
    let C := ENNReal.ofReal ((8 : ℝ) ^ (4*d+2))
    have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hzero : ENNReal.ofReal eta * volume (densityFailure E eta) = 0 := by
      apply le_antisymm ?_ bot_le
      apply le_of_forall_gt
      intro eps heps
      have hdiv : eps/C ≠ 0 := (ENNReal.div_pos_iff.mpr ⟨heps.ne', hCtop⟩).ne'
      obtain ⟨U, hEU, hU, _, herror⟩ := hE.exists_isOpen_sdiff_lt hfinite hdiv
      have hbound := (mul_le_mul_right (measure_mono
        (densityFailure_subset_error_maximal hE.nullMeasurableSet hU hEU))
        (ENNReal.ofReal eta)).trans
        (maximalCylinderUnion_weak_type (U \ E) (ENNReal.ofReal eta))
      have herr : C * volume (U \ E) < eps := by
        have h := ENNReal.mul_lt_mul_left hC0 hCtop herror
        rwa [mul_comm (volume (U \ E)) C, mul_comm (eps/C) C,
          ENNReal.mul_div_cancel hC0 hCtop] at h
      exact hbound.trans_lt herr
    exact (mul_eq_zero.mp hzero).resolve_left (ENNReal.ofReal_pos.mpr heta).ne'
  obtain ⟨M, hEM, hM, hME⟩ := hE.exists_measurable_superset_ae_eq
  have hMf : volume M ≠ ⊤ := by rwa [measure_congr hME]
  have hsub : densityFailure E eta ⊆ densityFailure M eta := by
    intro P hP
    refine ⟨hEM hP.1, ?_⟩
    intro r0 hr0
    obtain ⟨r, hr, hrr, hbad⟩ := hP.2 r0 hr0
    refine ⟨r, hr, hrr, ?_⟩
    rw [measure_congr (hME.inter Filter.EventuallyEq.rfl)]
    exact hbad
  exact measure_mono_null hsub (volume_densityFailure_eq_zero_of_measurable hM hMf)


/-- A single full-measure subset has near-full density at every positive threshold. -/
theorem ae_centeredCylinder_density_all {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E) :
    ∀ᵐ P ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
      ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
        (1-eta)*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal  := by
  have ae_centeredCylinder_density {eta : ℝ} (heta : 0 < eta) :
      ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 →
        (1-eta)*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
    have hzero := volume_densityFailure_eq_zero hE (volume_bounded_ne_top hbounded) heta
    have hae : ∀ᵐ P ∂volume, P ∉ densityFailure E eta := by
      apply ae_iff.mpr
      have heq : {P : KineticPoint d | ¬P ∉ densityFailure E eta} = densityFailure E eta := by
        ext P
        exact not_not
      rw [heq]
      exact hzero
    rw [ae_restrict_iff'₀ hE]
    filter_upwards [hae] with P hP hPE
    by_contra hnot
    apply hP
    refine ⟨hPE, ?_⟩
    intro r0 hr0
    by_contra hnone
    apply hnot
    refine ⟨r0, hr0, ?_⟩
    intro r hr hrr
    by_contra hbad
    exact hnone ⟨r, hr, hrr, lt_of_not_ge hbad⟩
  have hnat : ∀ n : ℕ, ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 →
        (1-1/((n : ℝ)+1))*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
    intro n
    exact ae_centeredCylinder_density (by positivity)
  filter_upwards [ae_all_iff.mpr hnat] with P hP
  intro eta heta
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt heta
  obtain ⟨r0, hr0, hsmall⟩ := hP n
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrr
  have h := hsmall r hr hrr
  have hvol := ENNReal.toReal_nonneg (a := volume (centeredCylinder P r))
  have hdiff : 1-eta ≤ 1-1/((n : ℝ)+1) := by exact sub_le_sub_left hn.le 1
  exact (mul_le_mul_of_nonneg_right hdiff hvol).trans h



/-- The unit backward cylinder used by the covering theorem. -/
def unitCylinder (d : ℕ) : Set (KineticPoint d) := backwardCylinder ⟨0, 0, 0⟩ 1

/-- Centers of a path retaining X while shrinking velocity toward the origin. -/
def saturationCenter {d : ℕ} (X : KineticPoint d) (r : ℝ) : KineticPoint d :=
  ⟨(1-r^2)*X.time, X.position+(((1-r^2)*X.time)-X.time) • ((1-r) • X.velocity),
    (1-r) • X.velocity⟩

/-- Native coordinate inequalities for membership in the unit cylinder. -/
theorem mem_unitCylinder_iff {d : ℕ} (X : KineticPoint d) :
    X ∈ unitCylinder d ↔ -1 < X.time ∧ X.time < 0 ∧
      PDE.vecEuclideanNorm X.velocity < 1 ∧ PDE.vecEuclideanNorm X.position < 1 := by
  simp only [unitCylinder, mem_backwardCylinder_iff, zero_sub, one_pow,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero,
    relativePosition, smul_zero]

/-- The point retained by the admissible path has zero relative position. -/
theorem relativePosition_saturationCenter {d : ℕ} (X : KineticPoint d) (r : ℝ) :
    relativePosition (saturationCenter X r) X = 0 := by
  ext i
  simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Every positive-radius path cylinder contains its point. -/
theorem self_mem_saturationCylinder {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r) :
    X ∈ backwardCylinder (saturationCenter X r) r := by
  obtain ⟨htlo, hthi, hv, _⟩ := (mem_unitCylinder_iff X).mp hX
  have hr2 := sq_pos_of_pos hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (1-r^2)*X.time-r^2 < X.time
    nlinarith
  · change X.time < (1-r^2)*X.time
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    have heq : X.velocity-(saturationCenter X r).velocity = r • X.velocity := by
      ext i
      simp only [saturationCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, PDE.vecEuclideanNorm_smul, abs_of_pos hr]
    nlinarith
  · rw [relativePosition_saturationCenter]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)

/-- Points of a path cylinder stay within r² in time of its retained point. -/
theorem saturationCylinder_time_bound {d : ℕ} {X Y : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r)
    (hY : Y ∈ backwardCylinder (saturationCenter X r) r) :
    |Y.time-X.time| < r^2 :=
  abs_time_sub_lt_sq hY (self_mem_saturationCylinder hX hr)

/-- The path is contained in the unit cylinder away from a spatial shell. -/
theorem saturationCylinder_subset_unit {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hR : R ≤ 1) (hx : PDE.vecEuclideanNorm X.position < 1-2*R^2) :
    backwardCylinder (saturationCenter X r) r ⊆ unitCylinder d := by
  have hRp : 0 < R := hr.trans_le hrR
  have hr1 : r ≤ 1 := hrR.trans hR
  obtain ⟨htlo, hthi, hv, _⟩ := (mem_unitCylinder_iff X).mp hX
  have hv0 := PDE.vecEuclideanNorm_nonneg X.velocity
  have hvc : PDE.vecEuclideanNorm (saturationCenter X r).velocity ≤ 1-r := by
    change PDE.vecEuclideanNorm ((1-r) • X.velocity) ≤ 1-r
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg (sub_nonneg.mpr hr1)]
    nlinarith
  intro Y hY
  apply (mem_unitCylinder_iff Y).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hbot : -1 ≤ (saturationCenter X r).time-r^2 := by
      change -1 ≤ (1-r^2)*X.time-r^2
      have : 0 ≤ 1-r^2 := by nlinarith
      nlinarith
    exact hbot.trans_lt hY.1
  · have htop : (saturationCenter X r).time ≤ 0 := by
      change (1-r^2)*X.time ≤ 0
      apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith
    exact hY.2.1.trans_le htop
  · have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hY.2.2.1
    have heq : Y.velocity = (Y.velocity-(saturationCenter X r).velocity)+
        (saturationCenter X r).velocity := by abel
    rw [heq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans_lt (by linarith)
  · have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (pow_pos hr 3)).mp hY.2.2.2
    rw [sub_zero] at hy
    have htime := saturationCylinder_time_bound hX hr hY
    have heq : Y.position = X.position+relativePosition (saturationCenter X r) Y+
        (Y.time-X.time) • (saturationCenter X r).velocity := by
      ext i
      simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    have hnorm := PDE.vecEuclideanNorm_add_le X.position
      (relativePosition (saturationCenter X r) Y)
    have hnorm2 := PDE.vecEuclideanNorm_add_le
      (X.position+relativePosition (saturationCenter X r) Y)
      ((Y.time-X.time) • (saturationCenter X r).velocity)
    have hmul : |Y.time-X.time| *PDE.vecEuclideanNorm (saturationCenter X r).velocity ≤ r^2 :=
      calc
        _ ≤ r^2*(1-r) := mul_le_mul htime.le hvc
          (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
        _ ≤ r^2 := by nlinarith [sq_nonneg r]
    rw [PDE.vecEuclideanNorm_smul] at hnorm2
    have hs : r^2 ≤ R^2 := by nlinarith
    have hc : r^3 ≤ r^2 := by nlinarith [sq_nonneg r]
    rw [heq]
    linarith

/-- A path cylinder fits in the centered kinetic cylinder of twice its radius. -/
theorem saturationCylinder_subset_centered {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r) :
    backwardCylinder (saturationCenter X r) r ⊆ centeredCylinder X (2*r) := by
  have hv := ((mem_unitCylinder_iff X).mp hX).2.2.1
  intro Y hY
  apply (mem_centeredCylinder_iff X Y (by positivity : 0 < 2*r)).mpr
  have ht := saturationCylinder_time_bound hX hr hY
  have hyv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hY.2.2.1
  have hyp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (pow_pos hr 3)).mp hY.2.2.2
  rw [sub_zero] at hyp
  have heq : (saturationCenter X r).velocity-X.velocity = (-r) • X.velocity := by
    ext i
    simp only [saturationCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hvc : PDE.vecEuclideanNorm ((saturationCenter X r).velocity-X.velocity) < r := by
    rw [heq, PDE.vecEuclideanNorm_smul, abs_neg, abs_of_pos hr]
    nlinarith
  have hvsum : Y.velocity-X.velocity =
      (Y.velocity-(saturationCenter X r).velocity)+
        ((saturationCenter X r).velocity-X.velocity) := by abel
  have hpsum : relativePosition X Y = relativePosition (saturationCenter X r) Y+
      (Y.time-X.time) • ((saturationCenter X r).velocity-X.velocity) := by
    ext i
    simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨by nlinarith [sq_pos_of_pos hr], ?_, ?_⟩
  · rw [hvsum]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans_lt (by linarith)
  · rw [hpsum]
    have hsum := PDE.vecEuclideanNorm_add_le (relativePosition (saturationCenter X r) Y)
      ((Y.time-X.time) • ((saturationCenter X r).velocity-X.velocity))
    rw [PDE.vecEuclideanNorm_smul] at hsum
    have hmul : |Y.time-X.time| *
        PDE.vecEuclideanNorm ((saturationCenter X r).velocity-X.velocity) ≤ r^3 := by
      have h := mul_le_mul ht.le hvc.le (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
      nlinarith
    nlinarith [pow_pos hr 3]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

