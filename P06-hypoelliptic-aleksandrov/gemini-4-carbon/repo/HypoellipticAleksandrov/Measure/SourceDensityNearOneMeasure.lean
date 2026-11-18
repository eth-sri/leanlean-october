module

public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped ENNReal Topology






/-- The normalized open coordinate box has volume `2^d`. -/
theorem volume_parabolicBox_one_toReal (d : Nat) :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal = (2 : Real) ^ d := by
  simpa using (volume_parabolicBox_toReal (vartheta := 1) (r := 1)
    (t₀ := 0) (v₀ := 0) (by norm_num) (by norm_num))


/-- The normalized open coordinate box has finite volume. -/
theorem volume_parabolicBox_one_ne_top (d : Nat) :
    volume (parabolicBox 1 1 0 (0 : PDE.Vec d)) ≠ ∞  := by
  intro htop
  have volume_parabolicBox_one_toReal_pos :
      0 < (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
    rw [volume_parabolicBox_one_toReal]
    positivity
  have hpos := volume_parabolicBox_one_toReal_pos
  rw [htop, ENNReal.toReal_top] at hpos
  linarith


/-- Real-valued corollary of the finite-support parabolic norm estimate. -/
theorem parabolicLpNormOn_le_of_norm_le_indicator
    (d : Nat) (f : TimeVelocity d → Real) (s E : Set (TimeVelocity d))
    (M : Real) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)
    (hfinite : volume (s ∩ E) ≠ ∞)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _ : TimeVelocity d ↦ M) z) :
    parabolicLpNormOn d f s ≤
      M * Real.rpow (volume (s ∩ E)).toReal (1 / ((d : Real) + 1))  := by
  have parabolicELpNormOn_le_of_norm_le_indicator :
      parabolicELpNormOn d f s ≤
      ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
    have parabolicExponent_toReal (d : Nat) :
        (parabolicExponent d).toReal = (d : Real) + 1 := by
      unfold parabolicExponent
      have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
      rw [hcast, ENNReal.toReal_natCast]
      norm_num
    have parabolicExponent_ne_top :
        parabolicExponent d ≠ ∞ := by
      simp [parabolicExponent]
    have parabolicExponent_ne_zero :
        parabolicExponent d ≠ 0 := by
      simp [parabolicExponent]
    have hmono : eLpNorm f (parabolicExponent d) (volume.restrict s) ≤
        eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
          (parabolicExponent d) (volume.restrict s) :=
      eLpNorm_mono_ae hf (ae_restrict_of_forall_mem hs (by
        intro z hz
        by_cases hzE : z ∈ E
        · simpa [Set.indicator_of_mem hzE, abs_of_nonneg hM]
            using hbound z hz
        · simpa only [Set.indicator_of_notMem hzE, norm_zero] using hbound z hz))
    calc
      parabolicELpNormOn d f s = eLpNorm f (parabolicExponent d) (volume.restrict s) := rfl
      _ ≤ eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
          (parabolicExponent d) (volume.restrict s) := hmono
      _ = ‖M‖ₑ * (volume.restrict s E) ^ (1 / (parabolicExponent d).toReal) :=
        eLpNorm_indicator_const hE.nullMeasurableSet (parabolicExponent_ne_zero)
          (parabolicExponent_ne_top)
      _ = ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
        rw [Measure.restrict_apply hE, inter_comm, parabolicExponent_toReal]
        rw [Real.enorm_of_nonneg hM]
  have hraw := parabolicELpNormOn_le_of_norm_le_indicator
  have hexponent : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hright : ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexponent hfinite)
  have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hright hraw) hright).mpr hraw
  unfold parabolicLpNormOn
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ← ENNReal.toReal_rpow] at hreal
  exact hreal

/-- The strict sublevel set is measurable relative to the unit box under the
local `C²` regularity supplied to `DensityToPoint`. -/
theorem measurableSet_parabolicBox_inter_lt_one_of_contDiffOn
    (d : Nat) (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U) :
    MeasurableSet (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1}) := by
  change MeasurableSet (parabolicBox 1 1 0 0 ∩ u ⁻¹' Iio 1)
  exact ((hu.continuousOn.mono hQU).isOpen_inter_preimage
    (isOpen_parabolicBox 1 1 0 0) isOpen_Iio).measurableSet

/-- Density of the non-strict superlevel set bounds its exact strict
sublevel complement in the normalized parabolic box. -/
theorem volume_parabolicBox_inter_lt_one_toReal_le_one_sub_mul
    (d : Nat) (beta : Real) (U : Set (TimeVelocity d))
    (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hdensity : beta *
        (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal ≤
      (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | 1 ≤ u z})).toReal) :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal ≤
      (1 - beta) * (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
  let Q : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  let L := Q ∩ {z | u z < 1}
  let H := Q ∩ {z | 1 ≤ u z}
  have hL : MeasurableSet L := by
    exact measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
  have hLsubset : L ⊆ Q := fun _ hz => hz.1
  have hdiff : Q \ L = H := by
    ext z
    simp only [L, H, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hzQ, hzL⟩
      exact ⟨hzQ, le_of_not_gt fun hlt => hzL ⟨hzQ, hlt⟩⟩
    · rintro ⟨hzQ, hzu⟩
      constructor
      · exact hzQ
      · rintro ⟨_, hlt⟩
        exact (not_lt_of_ge hzu) hlt
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, (inter_eq_right.mpr hLsubset), hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL
        (volume_parabolicBox_one_ne_top d))
  change beta * (volume Q).toReal ≤ (volume H).toReal at hdensity
  change (volume L).toReal ≤ (1 - beta) * (volume Q).toReal
  linarith

private theorem weightedSource_nonneg {d : Nat} (rho : Real) (u : TimeVelocity d → Real)
    (z : TimeVelocity d) (hrho : 0 ≤ rho) :
    0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0) := by
  positivity





private theorem memLp_restrict_of_continuousOn_unit_collar
    {d : Nat} {U : Set (TimeVelocity d)}
    {f : TimeVelocity d → Real} {s : Set (TimeVelocity d)}
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hf : ContinuousOn f U)
    (hs :
      s ⊆ parabolicClosedBox 1 1 0 (0 : PDE.Vec d)) :
    MemLp f (parabolicExponent d) (volume.restrict s) := by
  let K :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKmeas := hKcompact.measurableSet
  have hfK := hf.mono hclosed
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hfK
  have hfKmem :
      MemLp f (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hfK.aestronglyMeasurable hKmeas) M ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hM z hz
  exact hfKmem.mono_measure (Measure.restrict_mono_set volume hs)

/-- The exponentially weighted local norm of the supplied source plus the
near-one deficit forcing is bounded by the literal unit-box source norm and
the strict-low-set error. -/
theorem
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_source_add_one_sub_le
    (d : Nat) (hd : 0 < d) (rho : Real) (hrho : 0 ≤ rho)
    (U : Set (TimeVelocity d)) (Fsrc u : TimeVelocity d → Real)
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hFsrc : ContinuousOn Fsrc U)
    (hu_nonneg :
      IsNonnegativeOn u (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (hFsrc_nonneg :
      IsNonnegativeOn Fsrc (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (v0 : PDE.Vec d)
    (hv0 :
      v0 ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2 : Real)) :
    Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) *
            (Fsrc z + rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 (0 : PDE.Vec d)) +
        rho * Real.rpow
          (volume
            (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩
              {z | u z < 1})).toReal
          (1 / ((d : Real) + 1))   := by
  have measurableSet_localABPInterior :
      MeasurableSet (localABPInterior v0) := by
    unfold localABPInterior localABPAffine
    exact (parabolicAffine_measurableEmbedding (d := d)
      (by norm_num : 0 < (1 / 2 : Real))).measurableSet_image'
        (measurableSet_parabolicInterior 1 0)
  have exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le (hQU : parabolicBox 1 1 0 0 ⊆ U) :
      Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      rho * Real.rpow (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
        (1 / ((d : Real) + 1)) := by
    have parabolicLpNormOn_localABP_weighted_one_sub_le :
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
        rho * Real.exp (rho / 4) *
          Real.rpow (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
            (1 / ((d : Real) + 1)) := by
      let Q : Set (TimeVelocity d) := parabolicBox 1 1 0 0
      let E := Q ∩ {z | u z < 1}
      let f : TimeVelocity d → Real := fun z ↦
        Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0)
      have hM : 0 ≤ rho * Real.exp (rho / 4) := mul_nonneg hrho (Real.exp_pos _).le
      have hE : MeasurableSet E := by
        exact measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
      have hfinite : volume (localABPInterior v0 ∩ E) ≠ ∞ := by
        apply measure_ne_top_of_subset (show localABPInterior v0 ∩ E ⊆ Q by
          intro z hz
          exact hz.2.1)
        exact volume_parabolicBox_one_ne_top d
      have hEfinite : volume E ≠ ∞ := by
        apply measure_ne_top_of_subset (show E ⊆ Q by
          intro z hz
          exact hz.1)
        exact volume_parabolicBox_one_ne_top d
      have hbound : ∀ z ∈ localABPInterior v0, ‖f z‖ ≤
          E.indicator (fun _ : TimeVelocity d ↦ rho * Real.exp (rho / 4)) z := by
        rintro z ⟨w, hw, rfl⟩
        have hzQ :=
          localABPInterior_subset_parabolicBox_one hv0 ⟨w, hw, rfl⟩
        by_cases hlow : u (localABPAffine v0 w) < 1
        · have hzE : localABPAffine v0 w ∈ E := ⟨hzQ, hlow⟩
          rw [Set.indicator_of_mem hzE]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (weightedSource_nonneg rho u (localABPAffine v0 w) hrho)]
          have hmax : max (1 - u (localABPAffine v0 w)) 0 ≤ 1 := by
            apply max_le
            · linarith [hu_nonneg (localABPAffine v0 w) hzQ]
            · norm_num
          rcases mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩
          have htime : rho * ((localABPAffine v0 w).1 - 3 / 4) ≤ rho / 4 := by
            dsimp only [localABPAffine, parabolicAffine]
            nlinarith [(mul_le_mul_of_nonneg_left hw1.le hrho)]
          calc
            Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) *
                (rho * max (1 - u (localABPAffine v0 w)) 0) ≤
                Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) * (rho * 1) := by
              gcongr
            _ ≤ Real.exp (rho / 4) * (rho * 1) := by
              gcongr
            _ = rho * Real.exp (rho / 4) := by ring
        · rw [Set.indicator_of_notMem]
          · have hfzero : f (localABPAffine v0 w) = 0 := by
              dsimp only [f]
              rw [max_eq_right]
              · ring
              · exact sub_nonpos.mpr (le_of_not_gt hlow)
            rw [hfzero, norm_zero]
          · rintro ⟨_, hzlow⟩
            exact hlow hzlow
      change parabolicLpNormOn d f (localABPInterior v0) ≤ _
      calc
        parabolicLpNormOn d f (localABPInterior v0) ≤
            rho * Real.exp (rho / 4) *
              Real.rpow (volume (localABPInterior v0 ∩ E)).toReal
                (1 / ((d : Real) + 1)) := (parabolicLpNormOn_le_of_norm_le_indicator d f (localABPInterior v0) E (rho * Real.exp (rho / 4)) (show AEStronglyMeasurable f (volume.restrict (localABPInterior v0)) from (show ContinuousOn f (localABPInterior v0) from (by fun_prop : Continuous (fun z => Real.exp (rho * (z.1 - 3 / 4)))).continuousOn.mul (continuousOn_const.mul ((continuousOn_const.sub (hu.continuousOn.mono ((localABPInterior_subset_parabolicBox_one hv0).trans hQU))).sup continuousOn_const))).aestronglyMeasurable (measurableSet_localABPInterior)) (measurableSet_localABPInterior) hE hM hfinite hbound)
        _ ≤ rho * Real.exp (rho / 4) *
              Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.rpow_le_rpow ENNReal.toReal_nonneg
            · exact ENNReal.toReal_mono hEfinite
                (measure_mono (inter_subset_right : localABPInterior v0 ∩ E ⊆ E))
            · positivity
          · exact hM
        _ = _ := rfl
    have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
      calc
        Real.exp (-rho / 4) * Real.exp (rho / 4) =
            Real.exp ((-rho / 4) + rho / 4) := (Real.exp_add _ _).symm
        _ = Real.exp 0 := by
          congr 1
          ring
        _ = 1 := Real.exp_zero
    calc
      Real.exp (-rho / 4) * parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
          Real.exp (-rho / 4) *
            (rho * Real.exp (rho / 4) *
              Real.rpow (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
                (1 / ((d : Real) + 1))) :=
        mul_le_mul_of_nonneg_left parabolicLpNormOn_localABP_weighted_one_sub_le (Real.exp_pos _).le
      _ = rho * Real.rpow
          (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
            (1 / ((d : Real) + 1)) := by
        have hrearrange : Real.exp (-rho / 4) * (rho * Real.exp (rho / 4) *
            Real.rpow (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
              (1 / ((d : Real) + 1))) =
            rho * (Real.exp (-rho / 4) * Real.exp (rho / 4)) *
            Real.rpow (volume (parabolicBox 1 1 0 0 ∩ {z | u z < 1})).toReal
              (1 / ((d : Real) + 1)) := by
          ring
        rw [hrearrange]
        rw [hcancel]
        ring
  let Q :=
    parabolicBox 1 1 0 (0 : PDE.Vec d)
  let K :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  let L := localABPInterior v0
  let E := Q ∩ {z | u z < 1}
  let W : TimeVelocity d → Real :=
    fun z ↦ Real.exp (rho * (z.1 - 3 / 4))
  let S : TimeVelocity d → Real := fun z ↦ W z * Fsrc z
  let D : TimeVelocity d → Real := fun z ↦ W z * (rho * max (1 - u z) 0)
  let T : TimeVelocity d → Real :=
    fun z ↦ W z * (Fsrc z + rho * max (1 - u z) 0)
  have hQK : Q ⊆ K := by
    rintro ⟨t, v⟩ ⟨⟨ht0, ht1⟩, hv⟩
    exact ⟨⟨ht0.le, ht1.le⟩, fun i ↦ (hv i).le⟩
  have hLQ : L ⊆ Q := by
    simpa using
      (localABPInterior_subset_parabolicBox_one hv0)
  have hLK := hLQ.trans hQK
  have hLmeas : MeasurableSet L := by
    simpa using measurableSet_localABPInterior
  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have hScont : ContinuousOn S U := by
    dsimp only [S]
    exact hW.continuousOn.mul hFsrc
  have hdefCont : ContinuousOn (fun z ↦ rho * max (1 - u z) 0) U :=
    continuousOn_const.mul
      ((continuousOn_const.sub hu.continuousOn).sup continuousOn_const)
  have hDcont : ContinuousOn D U := by
    dsimp only [D]
    exact hW.continuousOn.mul hdefCont
  have hFQmem :
      MemLp Fsrc (parabolicExponent d) (volume.restrict Q) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hFsrc hQK
  have hSmem : MemLp S (parabolicExponent d) (volume.restrict L) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hScont hLK
  have hDmem : MemLp D (parabolicExponent d) (volume.restrict L) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hDcont hLK
  have hFQtop : parabolicELpNormOn d Fsrc Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFQmem.eLpNorm_ne_top
  have hStop : parabolicELpNormOn d S L ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hSmem.eLpNorm_ne_top
  have hDtop : parabolicELpNormOn d D L ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hDmem.eLpNorm_ne_top
  have hdENN : 1 ≤ (d : ENNReal) := by
    exact_mod_cast hd
  have hp : 1 ≤ parabolicExponent d := by
    calc
      1 ≤ (d : ENNReal) := hdENN
      _ ≤ (d : ENNReal) + 1 := le_add_of_nonneg_right bot_le
      _ = parabolicExponent d := rfl
  have hT : T = S + D := by
    funext z
    dsimp only [T, S, D, W, Pi.add_apply]
    ring
  have htriENN :
      parabolicELpNormOn d T L ≤
        parabolicELpNormOn d S L + parabolicELpNormOn d D L := by
    unfold parabolicELpNormOn
    rw [hT]
    exact eLpNorm_add_le hp
  have hsumTop :
      parabolicELpNormOn d S L + parabolicELpNormOn d D L ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hStop, hDtop⟩
  have htriRealRaw := ENNReal.toReal_mono hsumTop htriENN
  have htriReal :
      parabolicLpNormOn d T L ≤
        parabolicLpNormOn d S L + parabolicLpNormOn d D L := by
    unfold parabolicLpNormOn
    rw [ENNReal.toReal_add hStop hDtop] at htriRealRaw
    exact htriRealRaw
  have hsourcePointwise :
      ∀ z ∈ L, ‖S z‖ ≤ ‖Real.exp (rho / 4) * Fsrc z‖ := by
    intro z hz
    have hzQ : z ∈ Q := hLQ hz
    have htime : rho * (z.1 - 3 / 4) ≤ rho / 4 := by
      have hbase : z.1 - 3 / 4 ≤ 1 / 4 := by
        linarith [hzQ.1.2]
      nlinarith
    have hweight :
        Real.exp (rho * (z.1 - 3 / 4)) ≤ Real.exp (rho / 4) :=
      Real.exp_le_exp.mpr htime
    have hFz : 0 ≤ Fsrc z := hFsrc_nonneg z hzQ
    have hleft : 0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z :=
      mul_nonneg (Real.exp_pos _).le hFz
    have hright : 0 ≤ Real.exp (rho / 4) * Fsrc z :=
      mul_nonneg (Real.exp_pos _).le hFz
    change ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ ≤
      ‖Real.exp (rho / 4) * Fsrc z‖
    calc
      ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ =
          Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z := by
        rw [Real.norm_eq_abs, abs_of_nonneg hleft]
      _ ≤ Real.exp (rho / 4) * Fsrc z :=
        mul_le_mul_of_nonneg_right hweight hFz
      _ = ‖Real.exp (rho / 4) * Fsrc z‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hright]
  have hSmono :
      parabolicELpNormOn d S L ≤
        eLpNorm (fun z ↦ Real.exp (rho / 4) * Fsrc z)
          (parabolicExponent d) (volume.restrict L) := by
    exact eLpNorm_mono_ae hSmem.aestronglyMeasurable
      (ae_restrict_of_forall_mem hLmeas hsourcePointwise)
  have hFLQ :
      parabolicELpNormOn d Fsrc L ≤ parabolicELpNormOn d Fsrc Q := by
    exact eLpNorm_mono_measure Fsrc (Measure.restrict_mono_set volume hLQ)
  have hsourceENN :
      parabolicELpNormOn d S L ≤
        ENNReal.ofReal (Real.exp (rho / 4)) * parabolicELpNormOn d Fsrc Q := by
    calc
      parabolicELpNormOn d S L ≤
          eLpNorm (fun z ↦ Real.exp (rho / 4) * Fsrc z)
            (parabolicExponent d) (volume.restrict L) := hSmono
      _ = ENNReal.ofReal (Real.exp (rho / 4)) *
          parabolicELpNormOn d Fsrc L := by
        change eLpNorm ((Real.exp (rho / 4)) • Fsrc)
          (parabolicExponent d) (volume.restrict L) =
          ENNReal.ofReal (Real.exp (rho / 4)) *
            eLpNorm Fsrc (parabolicExponent d) (volume.restrict L)
        rw [eLpNorm_const_smul,
          Real.enorm_of_nonneg (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (rho / 4)) *
          parabolicELpNormOn d Fsrc Q :=
        mul_le_mul_right hFLQ _
  have hsourceRightTop :
      ENNReal.ofReal (Real.exp (rho / 4)) * parabolicELpNormOn d Fsrc Q ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFQtop
  have hsourceRealRaw := ENNReal.toReal_mono hsourceRightTop hsourceENN
  have hsourceReal :
      parabolicLpNormOn d S L ≤
        Real.exp (rho / 4) * parabolicLpNormOn d Fsrc Q := by
    unfold parabolicLpNormOn at hsourceRealRaw
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      at hsourceRealRaw
    exact hsourceRealRaw
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    calc
      Real.exp (-rho / 4) * Real.exp (rho / 4) =
          Real.exp ((-rho / 4) + rho / 4) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        congr 1
        ring
      _ = 1 := Real.exp_zero
  have hsourceCancelled :
      Real.exp (-rho / 4) * parabolicLpNormOn d S L ≤
        parabolicLpNormOn d Fsrc Q := by
    calc
      Real.exp (-rho / 4) * parabolicLpNormOn d S L ≤
          Real.exp (-rho / 4) *
            (Real.exp (rho / 4) * parabolicLpNormOn d Fsrc Q) :=
        mul_le_mul_of_nonneg_left hsourceReal (Real.exp_pos _).le
      _ = parabolicLpNormOn d Fsrc Q := by
        rw [← mul_assoc, hcancel, one_mul]
  have hdeficit' :
      Real.exp (-rho / 4) * parabolicLpNormOn d D L ≤
        rho * Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
    simpa using (exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le (hQK.trans hclosed))
  calc
    Real.exp (-rho / 4) * parabolicLpNormOn d T L ≤
        Real.exp (-rho / 4) *
          (parabolicLpNormOn d S L + parabolicLpNormOn d D L) :=
      mul_le_mul_of_nonneg_left htriReal (Real.exp_pos _).le
    _ = Real.exp (-rho / 4) * parabolicLpNormOn d S L +
        Real.exp (-rho / 4) * parabolicLpNormOn d D L := by ring
    _ ≤ parabolicLpNormOn d Fsrc Q +
        rho * Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) :=
      add_le_add hsourceCancelled hdeficit'
    _ = _ := rfl

end HypoellipticAleksandrov.Parabolic

