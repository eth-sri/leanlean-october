module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionInterface
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionNormRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceNormDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionHeight
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionDiagonal
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFunctions
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSecond
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffGlobalJets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellSource
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith

/-! # The unconditional measurable family from flattening and spatial smoothing -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set
open scoped Topology ENNReal

/- For any fixed internally justified geometry, the literal measurable family is
constructed by a separate spatial smoothing scale for each flattening scale. -/
theorem construction_measurableFamily_of_geometry {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (p R mu S : ℝ)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (hR : 0 < R) (hmu : 0 < mu) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hTS : barrierTime mu < S ^ 2)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) :
    MeasurableFamilyStatement d p (profileLowerEllipticity h) (profileUpperEllipticity h)
      ⟨barrierTime mu, 0, 0⟩ S := by
  obtain ⟨m, hm, hmargin⟩ : ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m := by
      obtain ⟨m, hm, hb⟩ : ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m := by
          have hK := isCompact_profile_unit_sublevel ha h
          have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
          have hne : ({q : XV d | profileFunction h q ≤ 1} : Set (XV d)).Nonempty :=
            ⟨0, by change profileFunction h 0 ≤ 1; rw [hzero]; norm_num⟩
          have hc : Continuous (fun q : XV d => PDE.vecNormSq q.2) :=
            PDE.contDiff_vecNormSq.continuous.comp continuous_snd
          obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
          exact ⟨PDE.vecNormSq q.2, hvel q hq, fun z hz => hmax hz⟩

        /- The velocity cutoff is one on the profile domain and zero beyond the barrier radius. -/
      refine ⟨(m + R ^ 2) / 2, by linarith only [hm], ?_⟩
      intro q hq
      have hh := hb q hq
      linarith only [hh, hm]

    /- On the strict inner region the packed cutoff is locally constant one. -/
  obtain ⟨r0, hr0, hsmall⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      flatteningOffset * Real.rpow r alpha ≤ 1 / 4 ∧
      2 * Real.rpow r alpha ≤ 7 / 8 := by
      have hc : 0 < flatteningOffset := zero_lt_one.trans flatteningOffset_bounds.1
      let a : ℝ := 1 / (4 * flatteningOffset)
      have hap : 0 < a := div_pos zero_lt_one (mul_pos (by norm_num) hc)
      let r0 : ℝ := Real.rpow a alpha⁻¹
      have hr0 : 0 < r0 := Real.rpow_pos_of_pos hap _
      have hpower : Real.rpow r0 alpha = a := Real.rpow_inv_rpow hap.le ha.ne'
      refine ⟨r0, hr0, ?_⟩
      intro r hr hrr
      have hp := Real.rpow_le_rpow hr.le hrr.le ha.le
      change Real.rpow r alpha ≤ Real.rpow r0 alpha at hp
      rw [hpower] at hp
      have hca : flatteningOffset * a = 1 / 4 := by dsimp [a]; field_simp
      have hb : flatteningOffset * Real.rpow r alpha ≤ 1 / 4 := by
        calc
          _ ≤ flatteningOffset * a := mul_le_mul_of_nonneg_left hp hc.le
          _ = _ := hca
      have hpow := (Real.rpow_pos_of_pos hr alpha).le
      have hco := mul_le_mul_of_nonneg_right flatteningOffset_bounds.1.le hpow
      constructor
      · exact hb
      · simp only [Real.rpow_eq_pow] at hb hpow hco ⊢
        nlinarith

    /- Any positive scales tending to zero give the exact stationary source norm decay. -/
  obtain ⟨r, hr, hlim⟩ : ∃ r : ℕ → ℝ, (∀ j, 0 < r j ∧ r j < r0) ∧ Tendsto r atTop (nhds 0) := by
    let r : ℕ → ℝ := fun j => r0 * (1 / ((j : ℝ) + 2))
    refine ⟨r, ?_, ?_⟩
    · intro j
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      constructor
      · exact mul_pos hr0 (div_pos zero_lt_one (by linarith))
      · change r0 * (1 / ((j : ℝ) + 2)) < r0
        have hi : 1 / ((j : ℝ) + 2) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
        simpa only [mul_one] using mul_lt_mul_of_pos_left hi hr0
    · have hh := (tendsto_add_atTop_iff_nat 1).2
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hh' : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (nhds 0) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
      simpa only [mul_zero] using hh'.const_mul r0
  have hscale (j : ℕ) : 2 * Real.rpow (r j) alpha ≤ 1 :=
    ((hsmall (r j) (hr j).1 (hr j).2).2).trans (by norm_num)
  have hheight (j : ℕ) : flatteningOffset * Real.rpow (r j) alpha ≤ 1 / 4 :=
    (hsmall (r j) (hr j).1 (hr j).2).1
  let T := barrierTime mu
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  let pE := ENNReal.ofReal p
  have hpE : 1 ≤ pE := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hp0 : pE ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : pE ≠ ∞ := ENNReal.ofReal_ne_top
  let U := fun j n => smoothedZeroExtendedProfile h (r j) mu R (standardMollifierSequence n)
  let g := fun j P => max (constructionIndicatorSource h (r j) mu R
    (KineticPoint.equivProd d P)) 0
  let f := fun j n P => max (backwardOperator (fun _t x v => profileMatrix h (x, v))
    (U j n) P) 0
  let error := fun j n => eLpNorm (fun P => f j n P - g j P) pE nu
  have herr (j : ℕ) : Tendsto (error j) atTop (𝓝 0) :=
    construction_positiveSource_error_tendsto hd ha ha1 h (r j) mu R m T S
      (hr j).1 hmu hR hm hS (hscale j) hmargin pE hp0 hpTop
  let good := fun j n =>
    (∀ P, P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S → U j n P = 0) ∧
    (∃ P ∈ Q, (1 / 4 : ℝ) ≤ U j n P)
  have hgood (j : ℕ) : ∀ᶠ n in atTop, good j n := by
    obtain ⟨P, hP, hh⟩ := construction_smoothed_interior_height_eventually h (r j) mu R S
      (hr j).1 hmu hR hS hTS (hscale j) (hheight j) hvel
    have _h_xinl_0 : ∀ᶠ n in atTop, ∀ P : KineticPoint d,
      P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
      smoothedZeroExtendedProfile h (r j) mu R (standardMollifierSequence n) P = 0 := by
      let r := (r j)
      obtain ⟨delta, hd, hb⟩ : ∃ delta : ℝ, 0 < delta ∧ ∀ (r mu R : ℝ) (phi : ContDiffBump (0 : XV d)),
          phi.rOut < delta → ∀ P : KineticPoint d,
          P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
          smoothedZeroExtendedProfile h r mu R phi P = 0 := by
          let box : Set (XV d) := {q | PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧
            PDE.vecNormSq q.2 < S ^ 2}
          have ho : IsOpen box :=
            (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_fst) continuous_const).inter
              (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_snd) continuous_const)
          have hsub : {q | profileFunction h q ≤ 1} ⊆ box := by
            intro q hq
            have hh := hgeom q hq
            have hx := PDE.vecEuclideanNorm_nonneg q.1
            have hv := PDE.vecEuclideanNorm_nonneg q.2
            have hs3 := pow_pos hS 3
            change PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧ PDE.vecNormSq q.2 < S ^ 2
            rw [← PDE.vecEuclideanNorm_sq, ← PDE.vecEuclideanNorm_sq]
            constructor <;> nlinarith
          have hK := isCompact_profile_unit_sublevel ha h
          obtain ⟨delta, hd, hb⟩ := hK.exists_thickening_subset_open ho hsub
          refine ⟨delta, hd, ?_⟩
          intro r mu R phi hphi P hP
          have hfaces : P.time = T - S ^ 2 ∨
              P.velocity ∈ PDE.euclideanSphere 0 S ∨
              P.position ∈ PDE.euclideanSphere 0 (S ^ 3) := by
            simpa only [relativePosition, sub_zero, smul_zero,
              mem_union, mem_ofPred_eq, or_assoc] using hP.2
          rcases hfaces with ht | hv | hx
          · apply smoothedZeroExtendedProfile_eq_zero_of_time
            change P.time = T - S ^ 2 at ht
            linarith
          · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
            intro hq
            have hh := hb (Metric.thickening_mono hphi.le _ hq)
            have he : PDE.vecNormSq P.velocity = S ^ 2 := by
              simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using hv
            exact (ne_of_lt hh.2) he
          · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
            intro hq
            have hh := hb (Metric.thickening_mono hphi.le _ hq)
            have he : PDE.vecNormSq P.position = (S ^ 3) ^ 2 := by
              simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using hx
            exact (ne_of_lt hh.1) he

        /- Every sufficiently late concrete mollifier preserves the complete boundary. -/
      have hr := standardMollifierSequence_rOut_tendsto (G := XV d)
      filter_upwards [hr.eventually (Iio_mem_nhds hd)] with n hn
      exact hb r mu R (standardMollifierSequence n) hn
    filter_upwards [_h_xinl_0, hh] with n hn hhP
    exact ⟨hn, P, hP, hhP⟩
  obtain ⟨scale, hs, heLim⟩ : ∃ scale : ℕ → ℕ,
      (∀ j, good j (scale j) ∧
        error j (scale j) < ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      Tendsto (fun j => error j (scale j)) atTop (nhds 0) := by
    classical
    have hchoose : ∀ j, ∃ k, good j k ∧
        error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
      intro j
      have hp : 0 < (1 / ((j : ℝ) + 1)) := by positivity
      have he : ∀ᶠ k in atTop,
          error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
        (herr j).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hp))
      exact ((hgood j).and he).exists
    choose scale hs using hchoose
    refine ⟨scale, hs, ?_⟩
    have hu : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => bot_le) (fun j => (hs j).2.le)
  refine ⟨profileMatrix h, fun j => U j (scale j),
    (selectedProfile_spec h).2.2.2.2.1, (selectedProfile_spec h).2.2.2.2.2.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact smoothedZeroExtendedProfile_contDiff ha h (r j) mu R (hr j).1 hmu hR hvel _
  · intro j P
    exact smoothedZeroExtendedProfile_nonneg h (r j) mu R _ P
  · intro j P hP
    exact (hs j).1.1 P hP
  · intro j
    exact (hs j).1.2
  · have hgLim : Tendsto (fun j => eLpNorm (g j) pE nu) atTop (𝓝 0) :=
      construction_indicatorSource_norm_tendsto hd ha ha1 h mu R m T S p hmu hR hm hS
        hrate hmargin hp he r (fun j => (hr j).1) hscale hlim
    have hu : Tendsto (fun j => error j (scale j) + eLpNorm (g j) pE nu)
        atTop (𝓝 0) := by
      simpa only [add_zero] using heLim.add hgLim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => bot_le)
    intro j
    have hn := eLpNorm_add_le (p := pE) (μ := nu)
      (f := fun P => f j (scale j) P - g j P) (g := g j) hpE
    have heq : (fun P => f j (scale j) P - g j P) + g j = f j (scale j) := by
      funext P
      simp only [Pi.add_apply, sub_add_cancel]
    rw [heq] at hn
    exact hn

/- The measurable family holds at the exact parameters already published to the
smooth-coefficient lane; all choices are those made in `counterParameters`. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
