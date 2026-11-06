module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.TorusLoops.Lemma314Corrected

public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open MeasureTheory

/-- The corrected Lemma 3.14 (`TorusLoops.lemma_3_14_corrected_limsup`) is consumed with its
actual square-box
boundary-decay premise and its limsup-in-height conclusion. -/
theorem corrected_lemma314_proved : corrected_lemma314 := by
  intro q hzero
  exact TorusLoops.lemma_3_14_corrected_limsup q hzero

section
variable (q : Set.Ici (1 : ℝ))
/-- The square-box premise required by the corrected Lemma 3.14 follows from the absence of
percolation for the critical free measure, which is derived in `RCMProof/RouteB.lean` from the
positive lower bound on the inverse correlation length. The rectangle and critical parameter
records are the same record, and the free-box limit is unique. -/
theorem lemma314_square_boundary_decay_of_nonpercolation
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0) :
    Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0) := by
  let θ := TorusLoops.rectangleFKParameters q
  have hθ : θ = FK.criticalParameters q := rfl
  let ν :=
    Classical.choose (FK.freeBoxLimit_existsUnique θ)
  have hweak :=
    (Classical.choose_spec (FK.freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive
  have hμ' : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ := by
    simp_all
  have hμν :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ' (FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak)
  have hnoν : ν.toMeasure (RCInfinite.infiniteAt (0, 0)) = 0 := by
    simp_all [Duality.infiniteClusterAt, Duality.cluster, RCInfinite.infiniteAt, RCInfinite.cluster]
  have hzeroReal : Filter.Tendsto
      (fun n => (ν.toMeasure (Zhang.boundaryConnectionEvent n)).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp ((Zhang.tendsto_boundaryConnection_zero_iff ν.toMeasure).2 hnoν)
    tauto
  tauto

/-- For a fixed even width, the normalized loop-observable log rate is
eventually bounded above once the one-arm input of the corrected Lemma 3.14 holds. This
supplies the ordinary real-sequence boundedness needed to read its limsup conclusion. -/
theorem windingLoopDensityLogRate_abs_bounded
    {N : ℕ} (hN : Even N) (hNp : 0 < N)
    (harm : TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      TorusLoops.windingLoopTailArmThreshold q 1) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => abs (TorusLoops.windingLoopDensityLogRate hN hNp q n)) := by
  let C₀ := TorusLoops.windingLoopDensityLogOffset q
  let C₁ := TorusLoops.windingLoopDensityLogSlope q
  have hC₀ := TorusLoops.windingLoopDensityLogOffset_nonneg q
  have hC₁ := TorusLoops.windingLoopDensityLogSlope_nonneg q
  have hC : 0 ≤ C₀ + C₁ := by linarith
  let K := C₁ / 2 + (C₀ + C₁) / 2
  have hbounded : ∀ᶠ n : ℕ in Filter.atTop,
      abs (TorusLoops.windingLoopDensityLogRate hN hNp q n) ≤ K := by
    filter_upwards [Filter.eventually_ge_atTop (9 * N)] with n hn
    have hrate := TorusLoops.abs_windingLoopDensityLogRate_le
      hN hNp q 1 n (by norm_num) (by omega) (by omega) (by omega)
    have hden : 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      simp
    have hrem :=
      div_le_div_of_nonneg_left hC (by norm_num) hden
    grind
  tauto

/-- A single width cutoff combines the limsup estimate of the corrected Lemma 3.14 with the one-arm
threshold needed to know the rate sequence is ordinarily bounded. -/
theorem lemma314_limsup_and_one_arm_cutoff
    (hzero : Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : {k : ℕ // 2 ≤ k}, ∀ (N : ℕ) (hN : Even N)
      (hNlarge : N₀.val ≤ N),
      Filter.limsup
        (fun n => abs (TorusLoops.windingLoopDensityLogRate hN (by omega) q n))
        Filter.atTop ≤ ε ∧
      TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
        TorusLoops.windingLoopTailArmThreshold q 1 := by
  obtain ⟨Nlim, hlim⟩ := corrected_lemma314_proved q hzero ε hε
  have hdecay := TorusLoops.tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero
  have harmEventually : ∀ᶠ N : ℕ in Filter.atTop,
      TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
        TorusLoops.windingLoopTailArmThreshold q 1 := by
    filter_upwards [hdecay.eventually (Iio_mem_nhds (TorusLoops.windingLoopTailArmThreshold_pos q 1))] with N hN
    linarith
  obtain ⟨Narm, harm⟩ := Filter.eventually_atTop.1 harmEventually
  refine ⟨⟨max Nlim.val Narm, ?_⟩, ?_⟩
  · omega
  grind
end

end PottsDiscontinuity.RCMProof
