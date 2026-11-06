module

public import HypoellipticAleksandrov.Measure.DensityNearOneMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Source bookkeeping for the near-one density argument

This module combines the supplied source and the near-one deficit in the
literal local parabolic norm.  It contains no PDE, ABP, or density argument.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set


private theorem memLp_restrict_of_continuousOn_unit_collar
    {d : Nat} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {f : TimeVelocity d → Real} {s : HypoellipticAleksandrov.Parabolic.Region d}
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hf : ContinuousOn f U)
    (hs :
      s ⊆ parabolicClosedBox 1 1 0 (0 )) :
    MemLp f (parabolicExponent d) (volume.restrict s) := by
  let K  :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact  :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKmeas  := hKcompact.measurableSet
  have hfK  := hf.mono hclosed
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hfK

  exact (show MemLp f (parabolicExponent d) (volume.restrict K) by
      refine MemLp.of_bound (hfK.aestronglyMeasurable hKmeas) M ?_
      filter_upwards [ae_restrict_mem hKmeas] with z hz
      exact hM z hz).mono_measure (Measure.restrict_mono_set volume hs)

/-- The exponentially weighted local norm of the supplied source plus the
near-one deficit forcing is bounded by the literal unit-box source norm and
the strict-low-set error. -/
theorem
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_source_add_one_sub_le
    (d : Nat) (hd : 0 < d) (rho : Real) (hrho : 0 ≤ rho)
    (U : HypoellipticAleksandrov.Parabolic.Region d) (Fsrc u : TimeVelocity d → Real)
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hFsrc : ContinuousOn Fsrc U)
    (hu_nonneg :
      IsNonnegativeOn u (parabolicBox 1 1 0 (0 )))
    (hFsrc_nonneg :
      IsNonnegativeOn Fsrc (parabolicBox 1 1 0 (0 )))
    (v0 : PDE.Vec d)
    (hv0 :
      v0 ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2 : Real)) :
    Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) *
            (Fsrc z + rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 (0 )) +
        rho * Real.rpow
          (volume
            (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩
              {z | u z < 1})).toReal
          (1 / ((d : Real) + 1)) := by
  let sharedTerm_596f1d70c9 := ((Real.exp (rho / 4)))
  let sharedTerm_60755bd65a := ((fun z ↦ Real.exp (rho / 4) * Fsrc z))
  let sharedTerm_4858cadd5b := ((1 / ((d : Real) + 1)))
  let Q  :=
    parabolicBox 1 1 0 (0 : PDE.Vec d)

  let L  := localABPInterior v0
  let E  := Q ∩ {z | u z < 1}
  let W : TimeVelocity d → Real :=
    fun z ↦ Real.exp (rho * (z.1 - 3 / 4))
  let S  := fun z ↦ W z * Fsrc z
  let D  := fun z ↦ W z * (rho * max (1 - u z) 0)
  let T  :=
    fun z ↦ W z * (Fsrc z + rho * max (1 - u z) 0)
  have hQK : Q ⊆ (parabolicClosedBox 1 1 0 (0 : PDE.Vec d)) := by
    rintro ⟨t, v⟩ ⟨⟨ht0, ht1⟩, hv⟩
    exact ⟨⟨ht0.le, ht1.le⟩, fun i ↦ (hv i).le⟩

  have hLQ : L ⊆ Q := by
    exact (localABPInterior_subset_parabolicBox_one hv0)
  have hLK  := hLQ.trans hQK

  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have hScont : ContinuousOn S U := by
    dsimp only [S]
    exact hW.continuousOn.mul hFsrc
  have hdefCont : ContinuousOn (fun z ↦ rho * max (1 - u z) 0) U :=
    continuousOn_const.mul
      ((continuousOn_const.sub hu.continuousOn).sup continuousOn_const)


  have hSmem  :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hScont hLK
  have hDmem  :=
    memLp_restrict_of_continuousOn_unit_collar hclosed (show ContinuousOn D U by
        dsimp only [D]
        exact hW.continuousOn.mul hdefCont) hLK

  have hStop : parabolicELpNormOn d S L ≠ ⊤ := by
    exact hSmem.eLpNorm_ne_top
  have hDtop : parabolicELpNormOn d D L ≠ ⊤ := by
    exact hDmem.eLpNorm_ne_top


  have hT : T = S + D := by
    funext z
    dsimp only [T, S, D, W, Pi.add_apply]
    ring


  have htriRealRaw := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hStop, hDtop⟩) (show parabolicELpNormOn d T L ≤
        parabolicELpNormOn d S L + parabolicELpNormOn d D L by
      unfold parabolicELpNormOn
      rw [hT]
      exact eLpNorm_add_le (show (1 : ENNReal) ≤ parabolicExponent d by
          calc
            (1 : ENNReal) ≤ (d : ENNReal) := (by
                exact_mod_cast hd)
            _ ≤ (d : ENNReal) + 1 := le_add_of_nonneg_right bot_le
            _ = parabolicExponent d := rfl))






  have hsourceRealRaw := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (show _ by
      exact (memLp_restrict_of_continuousOn_unit_collar hclosed hFsrc hQK).eLpNorm_ne_top)) (by
      calc
        parabolicELpNormOn d S L ≤
            eLpNorm sharedTerm_60755bd65a
              (parabolicExponent d) (volume.restrict L) := (by
                  exact eLpNorm_mono_ae hSmem.aestronglyMeasurable
                    (ae_restrict_of_forall_mem (by
                        exact measurableSet_localABPInterior v0) (by
                        intro z hz
                        have hzQ  := hLQ hz

                        have hweight  :=
                          Real.exp_le_exp.mpr (show rho * (z.1 - 3 / 4) ≤ rho / 4 by
                              have hbase : z.1 - 3 / 4 ≤ 1 / 4 := by
                                linarith [hzQ.1.2]
                              have hmul := mul_le_mul_of_nonneg_left hbase hrho
                              nlinarith)
                        have hFz  := hFsrc_nonneg z hzQ


                        change ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ ≤
                          ‖Real.exp (rho / 4) * Fsrc z‖
                        calc
                          ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ =
                              Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z := by
                            rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z from mul_nonneg (Real.exp_pos _).le hFz)]
                          _ ≤ Real.exp (rho / 4) * Fsrc z :=
                            mul_le_mul_of_nonneg_right hweight hFz
                          _ = ‖Real.exp (rho / 4) * Fsrc z‖ := by
                            rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.exp (rho / 4) * Fsrc z from mul_nonneg (Real.exp_pos _).le hFz)])))
        _ = ENNReal.ofReal sharedTerm_596f1d70c9 *
            parabolicELpNormOn d Fsrc L := by
          change eLpNorm (sharedTerm_596f1d70c9 • Fsrc)
            (parabolicExponent d) (volume.restrict L) =
            ENNReal.ofReal sharedTerm_596f1d70c9 *
              eLpNorm Fsrc (parabolicExponent d) (volume.restrict L)
          rw [eLpNorm_const_smul,
            Real.enorm_of_nonneg (Real.exp_pos _).le]
        _ ≤ ENNReal.ofReal sharedTerm_596f1d70c9 *
            parabolicELpNormOn d Fsrc Q :=
          mul_le_mul_right (show _ by
              exact eLpNorm_mono_measure Fsrc (Measure.restrict_mono_set volume hLQ)) _)
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

  have hdeficit :=
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le
      d rho hrho U u (hQK.trans hclosed) hu hu_nonneg v0 hv0

  calc
    Real.exp (-rho / 4) * parabolicLpNormOn d T L ≤
        Real.exp (-rho / 4) *
          (parabolicLpNormOn d S L + parabolicLpNormOn d D L) :=
      mul_le_mul_of_nonneg_left (by
          unfold parabolicLpNormOn
          rw [ENNReal.toReal_add hStop hDtop] at htriRealRaw
          exact htriRealRaw) (Real.exp_pos _).le
    _ = Real.exp (-rho / 4) * parabolicLpNormOn d S L +
        Real.exp (-rho / 4) * parabolicLpNormOn d D L := by ring
    _ ≤ parabolicLpNormOn d Fsrc Q +
        rho * Real.rpow (volume E).toReal sharedTerm_4858cadd5b :=
      add_le_add (by
          calc
            Real.exp (-rho / 4) * parabolicLpNormOn d S L ≤
                Real.exp (-rho / 4) *
                  (Real.exp (rho / 4) * parabolicLpNormOn d Fsrc Q) :=
              mul_le_mul_of_nonneg_left hsourceReal (Real.exp_pos _).le
            _ = parabolicLpNormOn d Fsrc Q := by
              rw [← mul_assoc, hcancel, one_mul]) (by
          exact hdeficit)
    _ = _ := by rfl

end HypoellipticAleksandrov.Parabolic
