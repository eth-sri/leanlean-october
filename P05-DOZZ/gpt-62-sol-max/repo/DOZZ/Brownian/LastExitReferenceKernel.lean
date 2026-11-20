/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedCylinderRead
public import DOZZ.Brownian.LastExitBrownianReferenceShift
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.WithDensity
public import DOZZ.Brownian.ConditionedKernelAlgebra

/-!
# Brownian reference kernel for the conditioned future

For a positive starting state, the Brownian path conditioned to stay below that state gives the
same positive Doob transition chain as the deterministic-time future of the entrance process.
This module packages the reference construction as a kernel, so finite-cylinder identities can
be transferred to the conditional future kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Rational evaluations of the positive path obtained by reflecting a drifted Brownian path
below its starting state. Nonpositive coordinates are assigned the initial state. -/
def brownianUpperConditionedPositiveRationalEvals (x : ℝ) (q : BrownianPath) : ℚ → ℝ :=
  fun r => brownianUpperConditionedPositivePath x q
    ⟨max (r : ℝ) 0, le_max_right _ _⟩

theorem measurable_brownianUpperConditionedPositiveRationalEvals :
    Measurable (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro r
  change Measurable (fun z : ℝ × BrownianPath =>
    z.1 - z.2 ⟨max (r : ℝ) 0, le_max_right _ _⟩)
  exact measurable_fst.sub
    ((ContinuousMap.measurable_eval _).comp measurable_snd)

theorem measurable_conditionedH_ref (ν : ℝ) : Measurable (conditionedH ν) := by
  unfold conditionedH
  split_ifs <;> fun_prop

/-- The joint raw-path density defining the upper-conditioned Brownian reference law. -/
noncomputable def brownianUpperConditionedRawDensity (ν : ℝ) (x : ℝ)
    (q : BrownianPath) : ℝ≥0∞ :=
  if _hx : 0 < x then
    (ENNReal.ofReal (conditionedH ν x))⁻¹ *
      ({q : BrownianPath | ∀ s : ℝ≥0,
        driftedBrownianPath (-ν) q s < x}.indicator (fun _ => 1) q)
  else 0

theorem measurable_brownianUpperConditionedRawDensity (ν : ℝ) :
    Measurable (Function.uncurry (brownianUpperConditionedRawDensity ν)) := by
  let D : ℝ × BrownianPath → ℝ × BrownianPath := fun z =>
    (z.1, driftedBrownianPath (-ν) z.2)
  have hD : Measurable D := measurable_fst.prodMk
      (continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_snd))
  have hsurv : MeasurableSet {z : ℝ × BrownianPath |
      ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1} := by
    let H : Set (ℝ × BrownianPath) := {z | ∃ s : ℝ≥0, z.1 ≤ z.2 s}
    have hh := measurableSet_brownianPath_joint_hit.preimage hD
    have heq : {z : ℝ × BrownianPath |
        ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1} =
        (D ⁻¹' H)ᶜ := by
      ext z
      simp [D, H, not_le]
    rw [heq]
    exact MeasurableSet.compl hh
  have hweight : Measurable (fun z : ℝ × BrownianPath =>
      if 0 < z.1 then (ENNReal.ofReal (conditionedH ν z.1))⁻¹ else 0) := by
    have hm : Measurable (fun z : ℝ × BrownianPath =>
        (ENNReal.ofReal (conditionedH ν z.1))⁻¹) :=
      (ENNReal.measurable_ofReal.comp
        ((measurable_conditionedH_ref ν).comp measurable_fst)).inv
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) hm
      measurable_const
  let w : ℝ × BrownianPath → ℝ≥0∞ := fun z =>
    if 0 < z.1 then (ENNReal.ofReal (conditionedH ν z.1))⁻¹ else 0
  let S : Set (ℝ × BrownianPath) :=
    {z | ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1}
  have heq : Function.uncurry (brownianUpperConditionedRawDensity ν) =
      fun z => w z * S.indicator (fun _ => 1) z := by
    funext z
    change (if hx : 0 < z.1 then
      (ENNReal.ofReal (conditionedH ν z.1))⁻¹ *
        ({q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < z.1}.indicator (fun _ => 1) z.2)
      else 0) = _
    by_cases hx : 0 < z.1
    · have hI : ({q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < z.1}.indicator
            (fun _ => (1 : ℝ≥0∞)) z.2) =
          S.indicator (fun _ => (1 : ℝ≥0∞)) z := by
        rfl
      simp only [dite_eq_left hx]
      rw [hI]
      simp [w, S, hx]
    · simp [w, S, hx]
  rw [heq]
  exact hweight.mul (measurable_const.indicator hsurv)

/-- The raw Brownian path law conditioned below its positive upper state, before applying the
drift map. -/
noncomputable def brownianUpperConditionedRawKernel (B : Measure BrownianPath) [SFinite B]
    (ν : ℝ) (hν : 0 < ν) :
    Kernel ℝ BrownianPath := by
  exact (Kernel.const ℝ B).withDensity (brownianUpperConditionedRawDensity ν)

instance isSFiniteKernel_brownianUpperConditionedRawKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedRawKernel B ν hν) := by
  unfold brownianUpperConditionedRawKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro x q
  unfold brownianUpperConditionedRawDensity
  split_ifs with hx
  · have hH := conditionedH_pos hν.le hx
    have hweight  :=
      ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hH)
    have hindicator : ({q : BrownianPath | ∀ s : ℝ≥0,
        driftedBrownianPath (-ν) q s < x}.indicator (fun _ => (1 : ℝ≥0∞)) q) ≤ 1 := by
      by_cases hq : q ∈ {q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < x}
      · simp [Set.indicator_of_mem hq]
      · simp [Set.indicator_of_notMem hq]
    have hbound :
        (ENNReal.ofReal (conditionedH ν x))⁻¹ *
            ({q : BrownianPath | ∀ s : ℝ≥0,
              driftedBrownianPath (-ν) q s < x}.indicator
                (fun _ => (1 : ℝ≥0∞)) q) < ⊤ := by
      calc
        (ENNReal.ofReal (conditionedH ν x))⁻¹ *
          ({q : BrownianPath | ∀ s : ℝ≥0,
            driftedBrownianPath (-ν) q s < x}.indicator
              (fun _ => (1 : ℝ≥0∞)) q) ≤
          (ENNReal.ofReal (conditionedH ν x))⁻¹ * 1 := by
            gcongr
        _ = (ENNReal.ofReal (conditionedH ν x))⁻¹ := by simp
        _ < ⊤ := hweight
    exact ne_of_lt hbound
  · simp

/-- Keep the starting state alongside its raw Brownian sample. -/
noncomputable def brownianUpperConditionedRawPairKernel (B : Measure BrownianPath)
    [SFinite B] (ν : ℝ) (hν : 0 < ν) : Kernel ℝ (ℝ × BrownianPath) :=
    (Kernel.parallelComp (Kernel.id : Kernel ℝ ℝ)
      (brownianUpperConditionedRawKernel B ν hν)) ∘ₖ
    Kernel.deterministic (fun x : ℝ => (x, x)) (by fun_prop)

instance isSFiniteKernel_brownianUpperConditionedRawPairKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedRawPairKernel B ν hν) := by
  unfold brownianUpperConditionedRawPairKernel
  infer_instance

theorem brownianUpperConditionedRawPairKernel_apply
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) (x : ℝ) :
    brownianUpperConditionedRawPairKernel B ν hν x =
      (Measure.dirac x).prod (brownianUpperConditionedRawKernel B ν hν x) := by
  rw [brownianUpperConditionedRawPairKernel,
    Kernel.comp_deterministic_eq_comap _ (by fun_prop)]
  simp [Kernel.comap_apply, Kernel.parallelComp_apply, Kernel.id_apply]

/-- Conditional future kernel obtained by the actual Brownian upper-conditioning construction. -/
theorem measurable_brownianUpperConditionedReferenceFutureMap (ν : ℝ) :
    Measurable (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1
        (driftedBrownianPath (-ν) z.2)) := measurable_brownianUpperConditionedPositiveRationalEvals.comp
    (measurable_fst.prodMk
      (continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_snd)))

noncomputable def brownianUpperConditionedReferenceFutureKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    Kernel ℝ (ℚ → ℝ) :=
  (Kernel.deterministic
    (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1
        (driftedBrownianPath (-ν) z.2))
    (measurable_brownianUpperConditionedReferenceFutureMap ν)) ∘ₖ
      brownianUpperConditionedRawPairKernel B ν hν

instance isSFiniteKernel_brownianUpperConditionedReferenceFutureKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedReferenceFutureKernel B ν hν) := by
  unfold brownianUpperConditionedReferenceFutureKernel
  infer_instance

section
variable (B : Measure BrownianPath) [SFinite B]

theorem brownianUpperConditionedReferenceFutureKernel_apply (ν : ℝ) (hν : 0 < ν) (x : ℝ) :
    brownianUpperConditionedReferenceFutureKernel B ν hν x =
      (brownianUpperConditionedRawKernel B ν hν x).map
        (fun q => brownianUpperConditionedPositiveRationalEvals x
          (driftedBrownianPath (-ν) q)) := by
  rw [brownianUpperConditionedReferenceFutureKernel,
    Kernel.deterministic_comp_eq_map
      (measurable_brownianUpperConditionedReferenceFutureMap ν),
    Kernel.map_apply _
      (measurable_brownianUpperConditionedReferenceFutureMap ν)]
  rw [brownianUpperConditionedRawPairKernel_apply,
    Measure.dirac_prod]
  rw [Measure.map_map
    (measurable_brownianUpperConditionedReferenceFutureMap ν)
    measurable_prodMk_left]
  congr 1

section
variable (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x)
include hx

theorem brownianUpperConditionedRawKernel_map_drifted :
    (brownianUpperConditionedRawKernel B ν hν x).map
        (driftedBrownianPath (-ν)) = brownianBelowConditionedLaw B ν x := by
  let E : Set BrownianPath := {q | ∀ s : ℝ≥0, driftedBrownianPath (-ν) q s < x}
  have hE : MeasurableSet E := by
    have hmD : Measurable (driftedBrownianPath (-ν)) :=
      continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_id)
    exact (measurableSet_brownianPath_below x).preimage hmD
  have hden : brownianUpperConditionedRawDensity ν x =
      E.indicator (fun _ => (ENNReal.ofReal (conditionedH ν x))⁻¹) := by
    funext q
    by_cases hq : q ∈ E
    · simp [brownianUpperConditionedRawDensity, E, hx, hq]
    · simp [brownianUpperConditionedRawDensity, E, hx, hq]
  have hraw : brownianUpperConditionedRawKernel B ν hν x =
      (ENNReal.ofReal (conditionedH ν x))⁻¹ • B.restrict E := by
    rw [brownianUpperConditionedRawKernel,
      Kernel.withDensity_apply _ (measurable_brownianUpperConditionedRawDensity ν)]
    rw [hden, withDensity_indicator hE, withDensity_const]
    simp [Kernel.const_apply]
  have hmD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  rw [hraw, brownianBelowConditionedLaw, Measure.map_smul _ hmD.aemeasurable]

theorem brownianUpperConditionedReferenceFutureKernel_apply_conditioned :
    brownianUpperConditionedReferenceFutureKernel B ν hν x =
    (brownianBelowConditionedLaw B ν x).map
        (fun q => brownianUpperConditionedPositiveRationalEvals x q) := by
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  have hcomp : (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x (driftedBrownianPath (-ν) q)) =
      (fun q => brownianUpperConditionedPositiveRationalEvals x q) ∘
        driftedBrownianPath (-ν) := rfl
  rw [brownianUpperConditionedReferenceFutureKernel_apply,
    hcomp, ← Measure.map_map hEval hD,
    brownianUpperConditionedRawKernel_map_drifted B ν x hν hx]

end

theorem isFiniteKernel_brownianUpperConditionedReferenceFutureKernel
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν : ℝ) (hν : 0 < ν) :
    IsFiniteKernel (brownianUpperConditionedReferenceFutureKernel B ν hν) := by
  refine ⟨1, ENNReal.one_lt_top, fun x => ?_⟩
  by_cases hx : 0 < x
  · let  :=
      isProbabilityMeasure_brownianBelowConditionedLaw B hB ν x hν hx
    have hprob : IsProbabilityMeasure
        (brownianUpperConditionedReferenceFutureKernel B ν hν x) := by
      rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
      infer_instance
    simp
  · have hraw : brownianUpperConditionedRawKernel B ν hν x = 0 := by
      unfold brownianUpperConditionedRawKernel
      ext s hs
      rw [Kernel.withDensity_apply _ (measurable_brownianUpperConditionedRawDensity ν)]
      have hdens : brownianUpperConditionedRawDensity ν x = 0 := by
        funext q
        simp [brownianUpperConditionedRawDensity, hx]
      rw [hdens]
      simp
    have hzero : brownianUpperConditionedReferenceFutureKernel B ν hν x = 0 := by
      rw [brownianUpperConditionedReferenceFutureKernel_apply, hraw]
      simp
    rw [hzero]
    simp

end

private theorem conditionedPositiveTransitionDensity_nonneg_ref
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (y : ℝ) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hx : 0 < x
  · exact conditionedPositiveTransitionDensity_nonneg hν ht hx y
  · simp [conditionedPositiveTransitionDensity, hν, ht, not_lt.mpr (le_of_not_gt hx)]

/-- The explicit finite Brownian Doob density is the real transition chain converted to an
`ENNReal` density on a cumulative elapsed schedule. -/
theorem brownianDoobFinitePDF_eq_chain_from_elapsed
    (ν t x : ℝ) (hν : 0 < ν) (n : ℕ) (ds : Fin n → ℝ≥0)
    (hds : ∀ i, 0 < ds i) (y : Fin n → ℝ) :
    ENNReal.ofReal (conditionedPositiveTimeChainDensity ν t x
      (List.ofFn fun i => t + (brownianFirstHitTimes n ds i : ℝ))
      (List.ofFn y)) = brownianDoobFinitePDF ν n ds x y := by
  induction n generalizing t x with
  | zero => simp [conditionedPositiveTimeChainDensity, brownianDoobFinitePDF]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [brownianFirstHitTimes, Fin.cons_zero, Fin.cons_succ,
        NNReal.coe_add, conditionedPositiveTimeChainDensity, add_sub_cancel_left]
      have hstepTime : 0 < (ds 0 : ℝ) := by exact_mod_cast hds 0
      rw [ENNReal.ofReal_mul
        (conditionedPositiveTransitionDensity_nonneg_ref (ν := ν)
          (t := (ds 0 : ℝ)) (x := x) hν.le hstepTime (y 0))]
      change _ * ENNReal.ofReal (conditionedPositiveTimeChainDensity ν
        (t + (ds 0 : ℝ)) (y 0)
        (List.ofFn fun i => t + ((ds 0 : ℝ) +
          (brownianFirstHitTimes n (Fin.tail ds) i : ℝ)))
        (List.ofFn (Fin.tail y))) = _
      simp_rw [← add_assoc]
      rw [ih (t + (ds 0 : ℝ)) (y 0) (Fin.tail ds)
        (fun i => hds i.succ) (Fin.tail y)]
      rfl

section
variable (B : Measure BrownianPath) [SFinite B] (hB : IsBrownianReal (fun t p => p t) B)
include hB

/-- The reference future at ordered positive rational offsets has the explicit finite Doob law. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection_doob
    (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets):
    (brownianUpperConditionedReferenceFutureKernel B ν hν x).map (fun y i => y (offsets i)) =
      volume.withDensity (brownianDoobFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i))) x) := by
  let ts := fun i => Real.toNNReal (offsets i)
  let ds := brownianFirstHitElapsed n ts
  have htimes : brownianFirstHitTimes n ds = ts :=
    brownianFirstHitTimes_elapsed_any (brownianPositiveOffsets_strictMono hoff hmono).monotone
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hproject : Measurable (fun y : ℚ → ℝ => fun i => y (offsets i)) :=
    measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  have hcompose : (fun y : ℚ → ℝ => fun i => y (offsets i)) ∘
      (fun q : BrownianPath => brownianUpperConditionedPositiveRationalEvals x q) =
        (fun q i => x - q (brownianFirstHitTimes n ds i)) := by
    rw [htimes]
    rfl
  rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx,
    Measure.map_map hproject hEval, hcompose]
  exact brownianBelowConditionedLaw_finite_positive_density_map B hB ν x hν hx n ds
    (brownianFirstHitElapsed_positiveOffsets hoff hmono)

/-- Every strictly ordered positive rational projection of the Brownian reference future has the
same finite Doob density as the deterministic-time conditioned future kernel. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection
    (ν t x : ℝ) (hν : 0 < ν) (hx : 0 < x)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (A : Set (Fin n → ℝ)) :
    (brownianUpperConditionedReferenceFutureKernel B ν hν x).map
        (fun y i => y (offsets i)) A =
      ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun z y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => z) y)) x A := by
  let ts := fun i => Real.toNNReal (offsets i)
  let ds := brownianFirstHitElapsed n ts
  have htimes : brownianFirstHitTimes n ds = ts :=
    brownianFirstHitTimes_elapsed_any (brownianPositiveOffsets_strictMono hoff hmono).monotone
  have htimes' : (fun i => t + (brownianFirstHitTimes n ds i : ℝ)) =
      fun i => t + (offsets i : ℝ) := by
    funext i
    rw [htimes, Real.coe_toNNReal _ (hoff i).le]
  have hinput : Measurable (fun z : ℝ × (Fin n → ℝ) => ((fun _ : Fin 1 => z.1), z.2)) :=
    (measurable_pi_iff.mpr fun _ => measurable_fst).prodMk measurable_snd
  have hD : Measurable (fun z : ℝ × (Fin n → ℝ) => conditionedPositiveFutureVectorDensity ν
      (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ)) (fun _ => z.1) z.2) :=
    (measurable_conditionedPositiveFutureVectorDensity ν
      (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))).comp hinput
  rw [brownianUpperConditionedReferenceFutureKernel_finite_projection_doob
    B hB ν x hν hx n offsets hoff hmono, Kernel.withDensity_apply _ hD x, Kernel.const_apply]
  congr 2
  funext y
  have h := brownianDoobFinitePDF_eq_chain_from_elapsed ν t x hν n ds
    (brownianFirstHitElapsed_positiveOffsets hoff hmono) y
  rw [htimes'] at h
  exact h.symm.trans (by simp [conditionedPositiveFutureVectorDensity])

end

section
variable {ν : ℝ} {P : Measure BrownianPath}

/-- The conditioned entrance state is strictly positive almost surely at every positive
deterministic time. -/
theorem conditionedPositiveStateAt_pos_ae (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∀ᵐ p ∂P, 0 < conditionedPositiveStateAt t p := by
  let times : Fin 1 → ℝ≥0 := fun _ => t
  have htimes : ∀ i, 0 < (times i : ℝ) := fun _ => ht
  have hmono : StrictMono times := by
    intro i j hij
    fin_cases i
    omega
  have hfd := negativeConditionedLaw_positiveFDD hP 1 (by norm_num)
    times htimes hmono
  let f : (Fin 1 → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (max 0
    (conditionedPositiveFDDDensity ν [t] [z 0]))
  have hfd' : P.map (fun p : BrownianPath => fun _ : Fin 1 => -(p t)) =
      (volume : Measure (Fin 1 → ℝ)).withDensity f := by
    assumption
  have heval : Measurable (fun z : Fin 1 → ℝ => z 0) := measurable_pi_apply 0
  have hvec : Measurable (fun p : BrownianPath => fun _ : Fin 1 => -(p t)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval t).neg
  have hmap : P.map (conditionedPositiveStateAt t) =
      ((volume : Measure (Fin 1 → ℝ)).withDensity f).map (fun z => z 0) := by
    calc
      P.map (conditionedPositiveStateAt t) =
          (P.map (fun p : BrownianPath => fun _ : Fin 1 => -(p t))).map
            (fun z => z 0) := by
          rw [Measure.map_map heval hvec]
          congr 1
      _ = _ := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun z => z 0)) hfd'
  have hnull : (P.map (conditionedPositiveStateAt t)) {x : ℝ | x ≤ 0} = 0 := by
    rw [hmap]
    calc
      (Measure.map (fun z : Fin 1 → ℝ => z 0)
          ((volume : Measure (Fin 1 → ℝ)).withDensity f)) {x : ℝ | x ≤ 0} =
        ((volume : Measure (Fin 1 → ℝ)).withDensity f)
          ((fun z : Fin 1 → ℝ => z 0) ⁻¹' {x : ℝ | x ≤ 0}) :=
        Measure.map_apply heval (measurableSet_le measurable_id measurable_const)
      _ = 0 := by
        have hpre : (fun z : Fin 1 → ℝ => z 0) ⁻¹' {x : ℝ | x ≤ 0} =
            {z : Fin 1 → ℝ | z 0 ≤ 0} := by ext z; rfl
        rw [hpre, withDensity_apply f
          (measurableSet_le (measurable_pi_apply 0) measurable_const)]
        apply setLIntegral_eq_zero
          (measurableSet_le (measurable_pi_apply 0) measurable_const)
        intro z hz
        simp [f, conditionedPositiveFDDDensity, conditionedPositiveEntranceDensity,
          hP.1, ht, not_lt.mpr hz]
  have hAE : ∀ᵐ x ∂P.map (conditionedPositiveStateAt t), 0 < x := by
    rw [ae_iff]
    simpa
  exact (ae_map_iff (μ := P) (f := conditionedPositiveStateAt t)
    (measurable_conditionedPositiveStateAt t).aemeasurable
    (p := fun x : ℝ => 0 < x)
    (measurableSet_lt measurable_const measurable_id)).1 hAE

/-- The joint endpoint/future law built from the abstract conditional kernel and from the actual
Brownian upper-conditioned reference kernel agree after every finite strictly ordered positive
rational projection. -/
theorem conditionedPositiveFutureKernel_reference_finite_compProd [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (hMonoEndpoint : StrictMono (Fin.append (fun _ : Fin 1 => t)
      (fun i => t + (offsets i : ℝ).toNNReal))) :
    let project : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
    let pairProject : (ℝ × (ℚ → ℝ)) → (ℝ × (Fin n → ℝ)) :=
      fun z => (z.1, project z.2)
    (((P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P).map
      pairProject) =
    (((P.map (conditionedPositiveStateAt t)) ⊗ₘ
      brownianUpperConditionedReferenceFutureKernel B ν hν).map pairProject) := by
  classical
  let project : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
  let pairProject : (ℝ × (ℚ → ℝ)) → (ℝ × (Fin n → ℝ)) :=
    fun z => (z.1, project z.2)
  let μx  := P.map (conditionedPositiveStateAt t)
  let κA  := conditionedPositiveFutureKernel t P
  let κR  := brownianUpperConditionedReferenceFutureKernel B ν hν
  have : IsSFiniteKernel κA := by dsimp [κA]; infer_instance
  have : IsSFiniteKernel κR := by dsimp [κR]; infer_instance
  let κD  :=
    (Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
      (fun x y => conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
        (fun _ => x) y)
  have hproject : Measurable project := measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have hpairProject : Measurable pairProject :=
    measurable_fst.prodMk (hproject.comp measurable_snd)
  have hstatePos  :=
    (ae_map_iff (μ := P) (f := conditionedPositiveStateAt t)
      (measurable_conditionedPositiveStateAt t).aemeasurable
      (p := fun x : ℝ => 0 < x)
      (measurableSet_lt measurable_const measurable_id)).2
      (conditionedPositiveStateAt_pos_ae hP t ht)
  have hrect : ∀ D, MeasurableSet D → ∀ C, MeasurableSet C →
      (((μx ⊗ₘ κA).map pairProject) (D ×ˢ C)) =
        (((μx ⊗ₘ κR).map pairProject) (D ×ˢ C)) := by
    intro D hD C hC
    have hpre : pairProject ⁻¹' (D ×ˢ C) = D ×ˢ (project ⁻¹' C) := by
      rfl
    have hleft : ((μx ⊗ₘ κA).map pairProject) (D ×ˢ C) =
        ∫⁻ x in D, κA.map project x C ∂μx := by
      rw [Measure.map_apply hpairProject (MeasurableSet.prod hD hC), hpre,
        Measure.compProd_apply_prod hD (hC.preimage hproject)]
      apply setLIntegral_congr_fun hD
      intro x hx
      change κA x (project ⁻¹' C) = κA.map project x C
      rw [Kernel.map_apply' _ hproject x hC]
    have hright : ((μx ⊗ₘ κR).map pairProject) (D ×ˢ C) =
        ∫⁻ x in D, κR.map project x C ∂μx := by
      rw [Measure.map_apply hpairProject (MeasurableSet.prod hD hC), hpre,
        Measure.compProd_apply_prod hD (hC.preimage hproject)]
      apply setLIntegral_congr_fun hD
      intro x hx
      change κR x (project ⁻¹' C) = κR.map project x C
      rw [Kernel.map_apply' _ hproject x hC]
    have hActual := conditionedPositiveFutureKernel_finite_projection_eq_density
      (hP := hP) t ht n offsets hoff hMonoEndpoint C hC
    have hReference (x : ℝ) (hx : 0 < x) :
        κR.map project x C = κD x C := by
      calc
        κR.map project x C =
            Measure.map project (brownianUpperConditionedReferenceFutureKernel B ν hν x) C := by
              rw [Kernel.map_apply _ hproject x]
        _ = κD x C := by
          simpa [κD, project] using
            (brownianUpperConditionedReferenceFutureKernel_finite_projection
          B hB ν t x hν hx n offsets hoff hmono C)
    have hkernelAE : ∀ᵐ x ∂μx, κA.map project x C = κR.map project x C := by
      filter_upwards [hActual, hstatePos] with x hA hx
      rw [hA, hReference x hx]
    exact hleft.trans ((setLIntegral_congr_fun_ae hD
      (hkernelAE.mono fun _ h _ => h)).trans hright.symm)
  have hfinite : ((μx ⊗ₘ κA).map pairProject) Set.univ < ∞ := measure_lt_top _ _
  have huniv : ((μx ⊗ₘ κA).map pairProject) Set.univ =
      ((μx ⊗ₘ κR).map pairProject) Set.univ := by
    simpa using hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  have heq := measure_eq_of_prod_rectangles
    ((μx ⊗ₘ κA).map pairProject) ((μx ⊗ₘ κR).map pairProject) hfinite hrect huniv
  simpa [μx, κA, κR, project, pairProject] using heq

end

section
variable (B : Measure BrownianPath) [SFinite B] (hB : IsBrownianReal (fun t p => p t) B) (ν x : ℝ)
  (hν : 0 < ν) (hx : 0 < x)
include hB hν hx

theorem brownianBelowConditionedLaw_eval_zero_ae :
    ∀ᵐ q ∂brownianBelowConditionedLaw B ν x, q 0 = 0 := by
  let drift : BrownianPath → BrownianPath := driftedBrownianPath (-ν)
  let S : Set BrownianPath := {p | ∀ t : ℝ≥0, drift p t < x}
  have hdrift : Measurable drift :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  have hS : MeasurableSet S := (measurableSet_brownianPath_below x).preimage hdrift
  have hzeroRestrict : ∀ᵐ p ∂B.restrict S, p 0 = 0 := by
    apply (ae_restrict_iff' hS).2
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    intro _
    exact hp
  have hzeroMap : ∀ᵐ q ∂(B.restrict S).map drift, q 0 = 0 := by
    rw [ae_map_iff hdrift.aemeasurable
      (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)]
    filter_upwards [hzeroRestrict] with p hp
    change drift p 0 = 0
    simp [drift, driftedBrownianPath, hp]
  have hH  := conditionedH_pos hν.le hx
  have hcoef : (ENNReal.ofReal (conditionedH ν x))⁻¹ ≠ 0 := by
    simp
  rw [brownianBelowConditionedLaw, MeasureTheory.Measure.ae_ennreal_smul_measure_iff hcoef]
  assumption

/-- The deterministic-time reference future starts at its prescribed positive state. -/
theorem brownianUpperConditionedReferenceFutureKernel_eval_zero_ae :
    ∀ᵐ y ∂brownianUpperConditionedReferenceFutureKernel B ν hν x, y 0 = x := by
  rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hzero : MeasurableSet {y : ℚ → ℝ | y 0 = x} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  rw [ae_map_iff hEval.aemeasurable hzero]
  filter_upwards [brownianBelowConditionedLaw_eval_zero_ae B hB ν x hν hx]
    with q hq
  simp only [brownianUpperConditionedPositiveRationalEvals,
    brownianUpperConditionedPositivePath]
  have hz : (⟨max ((0 : ℚ) : ℝ) 0,
      le_max_right ((0 : ℚ) : ℝ) 0⟩ : ℝ≥0) = 0 := by
    apply Subtype.ext
    norm_num
  rw [hz]
  change x - q 0 = x
  rw [hq]
  ring

end

section
variable {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
  (hP : IsNegativeConditionedBrownianLaw ν P) (B : Measure BrownianPath) [SFinite B]
  (hB : IsBrownianReal (fun t p => p t) B) (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
include hP hB ht

/-- The reference and abstract conditioned futures have the same full endpoint/future law.
Finite positive-time projections agree by the explicit density calculation; the rational
cylinder pi-system then gives equality on the entire future sequence. Nonpositive coordinates are
read from the endpoint, as both path constructions require. -/
theorem conditionedPositiveFutureKernel_reference_compProd :
    (P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P =
      (P.map (conditionedPositiveStateAt t)) ⊗ₘ
        brownianUpperConditionedReferenceFutureKernel B ν hν := by
  classical
  let m := P.map (conditionedPositiveStateAt t)
  let μ := m ⊗ₘ conditionedPositiveFutureKernel t P
  let ρ := m ⊗ₘ brownianUpperConditionedReferenceFutureKernel B ν hν
  have hstate : ∀ᵐ x ∂m, 0 < x :=
    ((ae_map_iff (measurable_conditionedPositiveStateAt t).aemeasurable
      (measurableSet_lt measurable_const measurable_id)).mpr (conditionedPositiveStateAt_pos_ae hP t ht))
  have hdiag : MeasurableSet {z : ℝ × (ℚ → ℝ) | ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1} :=
    measurableSet_agree_nonpos measurable_snd measurable_fst
  have hμ : ∀ᵐ z ∂μ, ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1 := by
    dsimp [μ, m]
    rw [conditionedPositiveFutureKernel_compProd,
      ae_map_iff ((measurable_conditionedPositiveStateAt t).prodMk
        (measurable_conditionedPositiveFutureRationalEvals t)).aemeasurable hdiag]
    exact Filter.Eventually.of_forall fun w _ => conditionedPositiveFutureRationalEvals_nonpos t w
  have hρ : ∀ᵐ z ∂ρ, ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1 := by
    apply Measure.ae_compProd_of_ae_ae hdiag
    filter_upwards [hstate] with x hx
    have hm : Measurable (brownianUpperConditionedPositiveRationalEvals x) :=
      measurable_brownianUpperConditionedPositiveRationalEvals.comp
        ((measurable_const (a := x)).prodMk measurable_id)
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
    apply (ae_map_iff hm.aemeasurable
      (measurableSet_agree_nonpos measurable_id (measurable_const (a := x)))).mpr
    filter_upwards [brownianBelowConditionedLaw_eval_zero_ae B hB ν x hν hx] with w hw q hq
    change x - w (q : ℝ).toNNReal = x
    rw [Real.toNNReal_eq_zero.mpr hq, hw, sub_zero]
  let e : ℝ × (ℚ → ℝ) ≃ᵐ (Fin 1 → ℝ) × (ℚ → ℝ) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.prodCongr (MeasurableEquiv.refl _)
  change μ = ρ
  apply e.measurableEmbedding.map_injective
  refine (identDistrib_of_prod_pi_fdd e.measurable.aemeasurable e.measurable.aemeasurable ?_).map_eq
  intro I J
  let p : ℚ → Prop := fun r => 0 < (r : ℝ)
  let n := (J.filter p).card
  let r : Fin n ↪o ℚ := (J.filter p).orderEmbOfFin rfl
  have hr i : p (r i) := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ _ _)).2
  obtain ⟨hm, hs⟩ := rationalFutureSchedule t r hr r.strictMono
  let project : ℝ × (ℚ → ℝ) → ℝ × (Fin n → ℝ) := fun z => (z.1, fun j => z.2 (r j))
  let read : ℝ × (Fin n → ℝ) → (I → ℝ) × (J → ℝ) :=
    fun z => (fun _ => z.1, readFiltered J p z.2 (fun _ => z.1))
  have hpj : Measurable project := measurable_fst.prodMk
    (measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).comp measurable_snd)
  have hc : Measurable read := (measurable_pi_iff.mpr fun _ => measurable_fst).prodMk
    (measurable_readFiltered J p measurable_snd (measurable_pi_iff.mpr fun _ => measurable_fst))
  have hread (z : ℝ × (ℚ → ℝ)) (hz : ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1) :
      read (project z) = Prod.map I.restrict J.restrict (e z) := by
    exact Prod.ext rfl (readFiltered_restrict J p z.2 _ fun q hq => (hz q (le_of_not_gt hq)).symm)
  exact map_eq_of_read hpj hpj hc (hμ.mono hread) (hρ.mono hread)
    (conditionedPositiveFutureKernel_reference_finite_compProd hP B hB t ht hν n r hr r.strictMono
      (strictMono_finAppend_endpoint hm hs))

/-- The actual conditional future kernel is the Brownian reference kernel at almost every state
of the entrance process. The joint-law identity above and uniqueness of disintegrations upgrade
the cylinder calculation to equality of the complete rational-path kernels. -/
theorem conditionedPositiveFutureKernel_eq_reference_ae :
    ∀ᵐ x ∂P.map (conditionedPositiveStateAt t),
      conditionedPositiveFutureKernel t P x =
        brownianUpperConditionedReferenceFutureKernel B ν hν x := by
  let := isFiniteKernel_brownianUpperConditionedReferenceFutureKernel B hB ν hν
  exact condDistrib_ae_eq_of_measure_eq_compProd
    (measurable_conditionedPositiveStateAt t).aemeasurable
    (measurable_conditionedPositiveFutureRationalEvals t).aemeasurable
    ((conditionedPositiveFutureKernel_compProd t P).symm.trans
      (conditionedPositiveFutureKernel_reference_compProd (hP := hP) B hB t ht hν))

end

end DOZZ.Proofs

end
