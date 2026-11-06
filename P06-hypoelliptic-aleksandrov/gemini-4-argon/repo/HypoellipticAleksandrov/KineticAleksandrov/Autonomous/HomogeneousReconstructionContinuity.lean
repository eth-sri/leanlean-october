module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionError
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGeometry
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Continuity of the actual bounded continuous-source potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/- Smooth compact native sources yield continuous physical potentials on the open strip. -/
theorem reconstruction_source_potential_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (g : BoundedBorel Point)
    (hg : ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T)) :
    ContinuousOn (stripSourcePotential H E.2 T g) (reconstructionStrip H sMinus T) := by
  intro p hp
  let a := (sMinus + p.time) / 2
  let R := |p.position 0| + 1
  have ha : sMinus < a := by dsimp only [a]; linarith only [hp.1]
  have hap : a < p.time := by dsimp only [a]; linarith only [hp.1]
  have hR : |p.position 0| < R := by dsimp only [R]; linarith
  have hc : ContinuousOn (stripSourcePotential H E.2 T g)
      {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R} := by
    classical
    let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    have hR (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨C, hC, hgb⟩ := g.exists_bound
    choose f hf hc hs hclose using fun n => exists_reconstruction_compact_source_approx
      H sMinus a T ha (hr n) (hR n) (hr n)
      (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x))) hg C hC
      (fun x => hgb _)
    have hfc (n : ℕ) : Continuous (f n) := (hf n).continuous
    have hfb (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f n x| ≤ B := by
      obtain ⟨B, hB⟩ := (hfc n).bounded_above_of_compact_support (hc n)
      refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
      have hh : |f n x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
      exact hh.trans (le_max_left _ _)
    let G (n : ℕ) : BoundedBorel Point :=
      ⟨fun p => f n (KineticPoint.equivProd 1 (sectionTwoPoint p)),
        (hfc n).measurable.comp
          ((KineticPoint.homeomorphProd 1).continuous.comp
            (continuous_sectionTwoPoint 1)).measurable, by
        obtain ⟨B, hB, hb⟩ := hfb n
        exact ⟨B, hB, fun p => hb _⟩⟩
    let F (n : ℕ) (p : Point) : ℝ :=
      duhamelPotential E.2 T (f n ∘ KineticPoint.equivProd 1) (sectionTwoPoint p)
    have hF (n : ℕ) : ContinuousOn (F n) (stripPast H T) := by
      let f := (f n)
      have hf := (hf n)
      have hc := (hc n)
      have hs := (hs n)
      have hg : ContDiff ℝ (⊤ : ℕ∞) (rawLift (f ∘ KineticPoint.equivProd 1)) := hf
      have hgc := hc.comp_homeomorph (KineticPoint.homeomorphProd 1)
      have hgs : tsupport (f ∘ KineticPoint.equivProd 1) ⊆
          evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
        intro p hp
        have hx := hs ((tsupport_comp_subset_preimage f
          (KineticPoint.homeomorphProd 1).continuous) hp)
        change sMinus < p.time ∧ p.time < T ∧ p.position 0 ∈ H.carrier at hx
        refine ⟨hx.2.1, ?_⟩
        apply PDE.mem_translateSet_iff_sub_mem.mpr
        simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
          PDE.vecOneCoordinate, Interval.carrier] using hx.2.2
      have hcont : ContinuousOn (duhamelPotential E.2 T (f ∘ KineticPoint.equivProd 1))
          (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
        let g := (f ∘ KineticPoint.equivProd 1)
        have hgU := hgs
        classical
        let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
        let U := (KineticPoint.equivProd 1).symm ⁻¹' D
        have hD : IsOpen D := isOpen_duhamelCylinder
          (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
          continuous_const T
        have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
        have hgcont : Continuous g := by
          have hh := hg.continuous.comp (KineticPoint.homeomorphProd 1).continuous
          exact hh
        have hK := hgc.isCompact.image (KineticPoint.homeomorphProd 1).continuous
        obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen hK hU
          (by
            rintro x ⟨p, hp, rfl⟩
            change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D
            simpa only [Equiv.symm_apply_apply] using hgU hp)
        let c := χ ∘ KineticPoint.equivProd 1
        have hcc : HasCompactSupport c := hc.comp_homeomorph (KineticPoint.homeomorphProd 1)
        have hcs : ContDiff ℝ (⊤ : ℕ∞) (rawLift c) := hχ
        have hccont : Continuous c := hχ.continuous.comp (KineticPoint.homeomorphProd 1).continuous
        have hcD : tsupport c ⊆ D := by
          intro p hp
          have hh := hs ((tsupport_comp_subset_preimage χ
            (KineticPoint.homeomorphProd 1).continuous) hp)
          change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hh
          simpa only [Equiv.symm_apply_apply] using hh
        obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
        let C := max B 0
        have hC : 0 ≤ C := le_max_right _ _
        have hgb : ∀ p, |g p| ≤ C := by
          intro p
          have hh : |g p| ≤ B := by simpa only [Real.norm_eq_abs] using hB p
          exact hh.trans (le_max_left _ _)
        let f : BoundedBorel Point := ⟨g, hgcont.measurable, ⟨C, hC, hgb⟩⟩
        let b : BoundedBorel Point := ⟨fun p => C * c p,
          measurable_const.mul hccont.measurable, ⟨C, hC, fun p => by
            change |C * χ (KineticPoint.equivProd 1 p)| ≤ C
            rw [abs_mul, abs_of_nonneg hC, abs_of_nonneg (hb _).1]
            exact mul_le_of_le_one_right hC (hb _).2⟩⟩
        have hb0 : ∀ p, 0 ≤ b p := fun p => mul_nonneg hC (hb _).1
        have hfb0 : ∀ p, 0 ≤ (f + b) p := by
          intro p
          change 0 ≤ g p + C * c p
          by_cases hp : g p = 0
          · rw [hp, zero_add]
            exact hb0 p
          · have hcp : c p = 1 := hone _ ⟨p, subset_tsupport _ hp, rfl⟩
            rw [hcp, mul_one]
            linarith only [neg_abs_le (g p), hgb p]
        have hbs : ContDiff ℝ (⊤ : ℕ∞) (rawLift b) := contDiff_const.mul hcs
        have hbc : HasCompactSupport (b : Point → ℝ) := hcc.mul_left
        have hbD : tsupport (b : Point → ℝ) ⊆ D :=
          (tsupport_mul_subset_right).trans hcD
        have hfbs : ContDiff ℝ (⊤ : ℕ∞) (rawLift (f + b)) := hg.add hbs
        have hfbc : HasCompactSupport (f + b : BoundedBorel Point) := hgc.add hbc
        have hfbD : tsupport (f + b : BoundedBorel Point) ⊆ D :=
          (tsupport_add _ _).trans (union_subset hgU hbD)
        have hcont (u : Point → ℝ) (hu0 : ∀ p, 0 ≤ u p)
            (hus : ContDiff ℝ (⊤ : ℕ∞) (rawLift u)) (huc : HasCompactSupport u)
            (huD : tsupport u ⊆ D) : ContinuousOn (duhamelPotential E.2 T u)
              (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
          obtain ⟨-, -, -, -, -, hcont, -⟩ :=
            kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
              hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
              (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
              (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
              E.1 E.2 hE T u hu0 hus huc huD
          exact hcont
        have hh := (hcont (f + b) hfb0 hfbs hfbc hfbD).sub (hcont b hb0 hbs hbc hbD)
        apply hh.congr
        intro p _
        have hs := strip_duhamel_sub H E.2 (f + b) b p T
        rw [add_sub_cancel_right] at hs
        exact hs
      apply hcont.comp (continuous_sectionTwoPoint 1).continuousOn
      intro p hp
      refine ⟨hp.1.le, subset_closure ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hFG (n : ℕ) (e : StripPole H (T : WithTop ℝ)) :
        stripPotentialOfKernel H E.2 T (G n) e = F n e.1 := by
      rw [← stripSourcePotential_eq_green H E.2 T (G n) e]
      unfold stripSourcePotential
      congr 1
    let Q := Real.exp ((max |H.lo| |H.hi| + 1) * (T - a)) * (2 * Real.exp R)
    let b (n : ℕ) : ℝ := r n * (T - a) + C *
      (Real.exp 1 * (2 * (r n) ^ 2 / lam) + r n + Q * r n)
    have hbd (n : ℕ) (p : Point)
        (hp : a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R) :
        |stripSourcePotential H E.2 T g p - F n p| ≤ b n := by
      let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.2.1.1, hp.2.1.2⟩
      have herr := reconstruction_green_potential_error hH hlam hLam A H E hE T a e hp.1
        g (G n) C hC (hr n) (hR n) (hr n).le (fun z hz => by
          have hh := hclose n (KineticPoint.equivProd 1 (sectionTwoPoint z)) hz
          rw [Equiv.symm_apply_apply, sectionTwoPoint_involutive] at hh
          simpa only [G, abs_sub_comm] using hh)
      rw [hFG] at herr
      rw [← stripSourcePotential_eq_green H E.2 T g e] at herr
      have hV : 0 ≤ max |H.lo| |H.hi| + 1 := by
        have hv := (abs_nonneg H.lo).trans (le_max_left |H.lo| |H.hi|)
        linarith only [hv]
      have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_left hp.1 T) hV)
      have hx := abs_le.mp hp.2.2
      have hxp := Real.exp_le_exp.mpr hx.2
      have hxm := Real.exp_le_exp.mpr (neg_le.mp hx.1)
      have hw : reconstructionSpatialWeight (p.position 0) ≤ 2 * Real.exp R := by
        unfold reconstructionSpatialWeight
        linarith only [hxp, hxm]
      have hQ : Real.exp ((max |H.lo| |H.hi| + 1) * (T - p.time)) *
          reconstructionSpatialWeight (p.position 0) ≤ Q :=
        mul_le_mul hex hw (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          (Real.exp_pos _).le
      apply herr.trans
      change _ ≤ b n
      dsimp only [b]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hp.1 T) (hr n).le
      · apply mul_le_mul_of_nonneg_left _ hC
        apply add_le_add (le_refl _)
        simpa only [r, div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hQ (hR n).le
    have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hb0 : Tendsto b atTop (𝓝 0) := by
      simpa only [b, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, add_zero] using
        (hr0.mul_const (T - a)).add
          ((((hr0.pow 2).const_mul 2).div_const lam).const_mul (Real.exp 1) |>.add hr0 |>.add
            (hr0.const_mul Q) |>.const_mul C)
    have hu : TendstoUniformlyOn F (stripSourcePotential H E.2 T g) atTop
        {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R} := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      filter_upwards [hb0.eventually (gt_mem_nhds hε)] with n hn
      intro p hp
      simpa only [Real.dist_eq] using (hbd n p hp).trans_lt hn
    exact hu.continuousOn (Eventually.of_forall fun n =>
      (hF n).mono (fun p hp => hp.2.1)).frequently
  have hpos : Continuous (fun q : Point => |q.position 0|) :=
    ((continuous_apply 0).comp continuous_position).abs
  have hn : {q : Point | a ≤ q.time ∧ q ∈ stripPast H T ∧ |q.position 0| ≤ R} ∈ 𝓝 p := by
    have h := (((isOpen_lt continuous_const continuous_time).inter
      (isOpen_stripPast H T)).inter (isOpen_lt hpos continuous_const)).mem_nhds
        ⟨⟨hap, hp.2⟩, hR⟩
    exact Filter.mem_of_superset h (fun q hq => ⟨hq.1.1.le, hq.1.2, hq.2.le⟩)
  exact (hc.continuousAt hn).continuousWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
