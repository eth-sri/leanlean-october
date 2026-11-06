module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.AssemblyArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Leakage
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DensityDefect
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageVolume
import Mathlib.Topology.Homeomorph.Lemmas
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationContinuity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationDensity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Differentiation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationRegular
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Indicator
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationFamily
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelay
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.TransportSlices
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry

/-! # Assembly for small radius cutoffs and small delayed height -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots

open Set MeasureTheory Covering
open HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
open scoped Topology
open Filter

/- Small-cutoff ink spots follow from critical density, delayed unions and the two shells. -/
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
      ((volume (F ∩ unitCylinder d)).toReal+coveringLeakage d*(m : ℝ)*R^2) := by
  have hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R :=
    fun P r hr hsub hd => (hstack P r hr hsub hd).1
  have hout : (volume (E \ criticalUnion E eta)).toReal ≤
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
      have hc : ∀ᵐ X ∂(volume.restrict E), PDE.vecEuclideanNorm X.position < 1-2*R^2 →
      ∃ P r, 0 < r ∧ r < R ∧ X ∈ backwardCylinder P r ∧
        backwardCylinder P r ⊆ unitCylinder d ∧
        (volume (E ∩ backwardCylinder P r)).toReal =
          (1-eta)*(volume (backwardCylinder P r)).toReal := by
        have hR1 := (hRsmall.trans (by norm_num : (1 : ℝ)/4 ≤ 1))
        have _h_xinl_2 : ∀ᵐ X ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
            ∃ r1 : ℝ, 0 < r1 ∧ ∀ r : ℝ, 0 < r → r < r1 →
              (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal ≤
                (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal := by
          have _h_xinl_0 : ∀ᵐ P ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
            ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
              (1-eta)*(volume (centeredCylinder P r)).toReal ≤
                (volume (E ∩ centeredCylinder P r)).toReal := by
            have hnat : ∀ n : ℕ, ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
                ∀ r : ℝ, 0 < r → r < r0 →
                  (1-1/((n : ℝ)+1))*(volume (centeredCylinder P r)).toReal ≤
                    (volume (E ∩ centeredCylinder P r)).toReal := by
              intro n
              exact ae_centeredCylinder_density hE hbounded (by positivity)
            filter_upwards [ae_all_iff.mpr hnat] with P hP
            intro eta heta
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt heta
            obtain ⟨r0, hr0, hsmall⟩ := hP n
            refine ⟨r0, hr0, ?_⟩
            intro r hr hrr
            have h := hsmall r hr hrr
            have hvol := ENNReal.toReal_nonneg (a := volume (centeredCylinder P r))
            have hdiff := sub_le_sub_left hn.le 1
            exact (mul_le_mul_of_nonneg_right hdiff hvol).trans h
          filter_upwards [_h_xinl_0, ae_restrict_mem₀ hE]
            with X hX hXE
          intro eta heta
          let k : ℝ := 2^(4*d+2)
          have hk : 0 < k := by positivity
          obtain ⟨s, hs, hsmall⟩ := hX (eta/k) (div_pos heta hk)
          refine ⟨s/2, half_pos hs, ?_⟩
          intro r hr hrr
          have _h_xinl_1 : backwardCylinder (saturationCenter X r) r ⊆ centeredCylinder X (2*r) := by
            have hX := (hEQ hXE)
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
          apply density_transfer_subset hE _h_xinl_1
            (volume_cylinder_pos_ne_top (centeredTop X (2*r)) (by positivity)).2 hk
          · unfold centeredCylinder
            rw [volume_cylinder_eq_unit _ (by positivity : 0 < 2*r),
              volume_cylinder_eq_unit _ hr, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*r)^(4*d+2)),
              ENNReal.toReal_ofReal (by positivity : 0 ≤ r^(4*d+2)), mul_pow]
            ring
          · exact hsmall (2*r) (by positivity) (by linarith)
        filter_upwards [_h_xinl_2, ae_restrict_mem₀ hE]
          with X hd hXE
        intro hx
        obtain ⟨s, hs, hsmall⟩ := hd (eta/2) (half_pos heta)
        let a := min s R/2
        have ha := half_pos (lt_min hs hR)
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
          have _h_xinl_0 : ContinuousAt (saturationGap E eta X) r := by
            have hE := (volume_bounded_ne_top hbounded)
            have hr := (ha.trans_le hr.1)
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
            have _h_xinl_0 : ContinuousAt (fun s => (volume (E ∩ backwardCylinder ((saturationCenter X) s) s)).toReal) r := by
              let P := (saturationCenter X)
              have hP : Continuous (saturationCenter X) := by
                apply KineticPoint.continuous_mk <;> fun_prop

              change Tendsto _ (𝓝 r) (𝓝 _)
              let : IsFiniteMeasure (volume.restrict E) :=
                ⟨by rw [Measure.restrict_apply_univ]; exact hE.lt_top⟩
              have _h_xinl_0 : ∀ᵐ Y ∂volume, ∀ᶠ s in 𝓝 r, Y ∈ backwardCylinder (P s) s ↔ Y ∈ backwardCylinder (P r) r := by
                have hvface :=
                  volume_velocity_sphere_face (P r).velocity hr
                have hpface : volume {Y : KineticPoint d |
                    PDE.vecNormSq (relativePosition (P r) Y) = (r^3)^2} = 0 := by
                  simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using
                    volume_position_sphere_face (P r) (pow_pos hr 3)
                filter_upwards [ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time)
                    ((P r).time-r^2) (volume_time_face _),
                  ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time) (P r).time (volume_time_face _),
                  ae_ne_of_null_fiber _ _ hvface, ae_ne_of_null_fiber _ _ hpface] with Y ht₁ ht₂ hv hp
                have ht := continuous_time.comp hP
                have hx := continuous_position.comp hP
                have hvp := continuous_velocity.comp hP
                have hrel : Continuous (fun s => relativePosition (P s) Y) :=
                  (continuous_const.sub hx).sub ((continuous_const.sub ht).smul hvp)
                have e₁ := eventually_lt_iff_of_ne (ht.sub (continuous_id.pow 2)).continuousAt
                  continuous_const.continuousAt ht₁.symm
                have e₂ := eventually_lt_iff_of_ne continuous_const.continuousAt ht.continuousAt ht₂
                have e₃ := eventually_lt_iff_of_ne
                  (PDE.continuous_vecNormSq.comp (continuous_const.sub hvp)).continuousAt
                  (continuous_id.pow 2).continuousAt hv
                filter_upwards [e₁, e₂, e₃, (eventually_lt_iff_of_ne (PDE.continuous_vecNormSq.comp hrel).continuousAt ((continuous_id.pow 3).pow 2).continuousAt hp)] with s h₁ h₂ h₃ h₄
                simpa only [backwardCylinder, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq,
                  sub_zero, Pi.sub_apply, Pi.pow_apply, Function.comp_apply, id_eq] using
                    and_congr h₁ (and_congr h₂ (and_congr h₃ h₄))
              have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 r)
                (μ := volume.restrict E) (isOpen_cylinder (P r) r).measurableSet
                (fun s => (isOpen_cylinder (P s) s).measurableSet)
                (ae_restrict_of_ae _h_xinl_0)
              have hreal := (ENNReal.continuousAt_toReal (measure_ne_top
                (volume.restrict E) (backwardCylinder (P r) r))).tendsto.comp hlim
              simpa only [Measure.restrict_apply (isOpen_cylinder _ _).measurableSet, inter_comm,
                Function.comp_def]
                using hreal
            exact _h_xinl_0.sub (continuousAt_const.mul hV)
          exact _h_xinl_0.continuousWithinAt
        obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' haR.le hc ⟨hneg.le, hpos.le⟩
        have hrpos := ha.trans_le hr.1
        have hrR := lt_of_le_of_ne hr.2 (by
          intro he
          rw [he] at heq
          linarith)
        refine ⟨saturationCenter X r, r, hrpos, hrR,
          self_mem_saturationCylinder (hEQ hXE) hrpos,
          saturationCylinder_subset_unit (hEQ hXE) hrpos hrR.le hR1 hx, ?_⟩
        dsimp [saturationGap] at heq
        linarith
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
      have _h_xinl_0 : (volume (unitCylinder d \ spatialCore d R)).toReal ≤ 2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
        have hrad : 0 < 1-2*R^2 := by nlinarith
        have hcore : NullMeasurableSet (spatialCore d R) volume :=
          (isOpen_roundBox d (-1) 0 (1-2*R^2)).measurableSet.nullMeasurableSet
        have _h_inl_15 : spatialCore d R ⊆ unitCylinder d := by
          have hrad : 0 < 1-2*R^2 := by nlinarith
          intro X hX
          apply (mem_unitCylinder_iff X).mpr
          refine ⟨hX.1, hX.2.1, ?_, ?_⟩
          · simpa only [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
              using hX.2.2.2
          · have hp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrad).mp hX.2.2.1
            rw [sub_zero] at hp
            nlinarith [sq_nonneg R]
        rw [volume_sdiff_toReal_of_subset hcore
          _h_inl_15
          (volume_cylinder_pos_ne_top _ zero_lt_one).2]
        rw [spatialCore, volume_roundBox_toReal d (by norm_num) hrad]
        have hp := one_sub_pow_lower d (by positivity : 0 ≤ 2*R^2)
          (by nlinarith : 2*R^2 ≤ 1)
        nlinarith only [mul_le_mul_of_nonneg_right hp (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))]
      exact (ENNReal.toReal_mono hf (measure_mono_ae hsub)).trans
        _h_xinl_0

    /- Exact-density cylinders yield a fixed proportional density reduction in their union. -/
  have hred : (volume (E ∩ criticalUnion E eta)).toReal ≤
      (1-eta/((8 : ℝ)^(4*d+2)))*(volume (criticalUnion E eta)).toReal := by
    have heta := heta.le
    have _h_xinl_0 : criticalUnion E eta ⊆ unitCylinder d := by
      intro X hX
      obtain ⟨z, hz, hmem⟩ := mem_iUnion₂.mp hX
      exact hz.2.1 hmem
    have hf : volume (criticalUnion E eta) ≠ ⊤ :=
      ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
        (measure_mono _h_xinl_0)
    exact cylinder_union_density_reduction Prod.fst Prod.snd (criticalParameters E eta) R
      (fun _ hz => hz.1)
      (fun z hz => (hcutoff z.1 z.2 hz.1 hz.2.1 (le_of_eq hz.2.2.symm)).le)
      E hE hf heta (fun _ hz => hz.2.2.le)
  have hdelay : (volume (criticalUnion E eta)).toReal ≤ (((m : ℝ)+1)/(m : ℝ))*((volume (F ∩ unitCylinder d)).toReal+ 2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2)) := by
    have hR1 : R ≤ 1 := (hRsmall.trans (by norm_num))
    obtain ⟨T, hT, hTc, hcover⟩ : ∃ T ⊆ criticalParameters E eta, T.Countable ∧
        (⋃ z ∈ T, backwardCylinder z.1 z.2) = criticalUnion E eta := by
        let : SecondCountableTopology (KineticPoint d) :=
          (KineticPoint.homeomorphProd d).secondCountableTopology
        exact TopologicalSpace.isOpen_biUnion_countable (criticalParameters E eta)
          (fun z => backwardCylinder z.1 z.2) (fun z _ => isOpen_cylinder z.1 z.2)


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
    have hboxfinite := volume_roundBox_ne_top d (-1) ((m : ℝ)*R^2)
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
        simpa only [mul_assoc] using leakage_shell_volume d hheight0 hheight
      linarith only [hreal, hshell]
    have hH : (⋃ z : T, backwardCylinder (P z) (r z)) = criticalUnion E eta := by
      rw [iUnion_subtype]
      exact hcover
    have hdelay : volume (⋃ i, backwardCylinder (P i) (r i)) ≤
        ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
          volume (⋃ i, openForwardStack (P i) (r i) m) := by
      have hr := (fun z => (hz z).1)
      rw [volume_transport_slices (isOpen_iUnion (fun i => isOpen_cylinder (P i) (r i))).measurableSet,
        volume_transport_slices
          (isOpen_iUnion (fun i => isOpen_openForwardStack (P i) (r i) m)).measurableSet,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro v
      dsimp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun y => delayed_union_slice P r hr m hm v y
    rw [hH] at hdelay
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfinite) hdelay
    have hq : 0 ≤ ((m : ℝ)+1)/(m : ℝ) := by positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_left hJbound hq)
  have hEfinite : volume E ≠ ⊤ := volume_bounded_ne_top hbounded
  have hIfinite : volume (E ∩ criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top hEfinite (measure_mono inter_subset_left)
  have hDfinite : volume (E \ criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top hEfinite (measure_mono sdiff_subset)
  have _h_xinl_0 : IsOpen (criticalUnion E eta) := by
      exact (
    isOpen_biUnion fun z _ => isOpen_cylinder z.1 z.2
    )
  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) E
    _h_xinl_0.measurableSet.nullMeasurableSet)
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
