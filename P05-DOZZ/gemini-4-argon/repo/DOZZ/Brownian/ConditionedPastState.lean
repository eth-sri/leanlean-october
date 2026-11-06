/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureKernelMarkov
public import DOZZ.Brownian.ConditionedFDDMarkovKernel
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# A finite conditioned past and one later state

The exact finite past/future density is transported from the one-coordinate future vector to
its real coordinate. This is the deterministic-time factorization used for marked last exits.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- The one-state transition kernel after a finite past, with its literal zero density at
nonpositive past endpoints. -/
noncomputable def conditionedPastStateKernel (ν dt : ℝ) (k : ℕ) :
    Kernel (Fin (k+1) → ℝ) ℝ :=
  (Kernel.const (Fin (k+1) → ℝ) (volume : Measure ℝ)).withDensity
    (fun x y => ENNReal.ofReal (max 0
      (conditionedPositiveTransitionDensity ν dt (x (Fin.last k)) y)))

theorem measurable_conditionedPastStateKernel_density ν dt k :
    Measurable (fun z : (Fin (k+1) → ℝ) × ℝ => ENNReal.ofReal (max 0
      (conditionedPositiveTransitionDensity ν dt (z.1 (Fin.last k)) z.2))) := by
  exact ((measurable_const (a := (0 : ℝ))).max (by exact (measurable_conditionedPositiveTransitionDensity_pair ν dt).comp (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd : Measurable (fun z : (Fin (k+1) → ℝ) × ℝ => (z.1 (Fin.last k), z.2))))).ennreal_ofReal

instance (ν dt : ℝ) (k : ℕ) : IsSFiniteKernel (conditionedPastStateKernel ν dt k) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

/-- The explicit finite past followed by a scalar deterministic-time state. -/
theorem negativeConditionedLaw_finitePast_state_compProd
    {ν} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    k (ss : Fin (k+1) → ℝ≥0) (hs : ∀ i, 0 < (ss i : ℝ))
    (hmono : StrictMono ss) (u : ℝ≥0) (hu : ss (Fin.last k) < u) :
    P.map (fun p : BrownianPath => (fun i => -(p (ss i)), -(p u))) =
      ((volume : Measure (Fin (k+1) → ℝ)).withDensity
        (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))) ⊗ₘ
        conditionedPastStateKernel ν ((u : ℝ)-(ss (Fin.last k) : ℝ)) k := by
  let future : Fin 1 → ℝ≥0 := fun _ => u
  let κ : Kernel (Fin (k+1) → ℝ) (Fin 1 → ℝ) :=
    (Kernel.const (Fin (k+1) → ℝ) (volume : Measure (Fin 1 → ℝ))).withDensity
      (conditionedPositiveFutureVectorDensity ν (fun i => (ss i : ℝ)) (fun _ => (u : ℝ)))
  have hκmeas := measurable_conditionedPositiveFutureVectorDensity ν
    (fun i => (ss i : ℝ)) (fun _ : Fin 1 => (u : ℝ))
  have : IsSFiniteKernel κ := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique fun _ => ℝ
  have hmapKernel : κ.map e =
      conditionedPastStateKernel ν ((u : ℝ)-(ss (Fin.last k) : ℝ)) k := by
    ext x : 1
    have hslice : Measurable (conditionedPositiveFutureVectorDensity ν
        (fun i => (ss i : ℝ)) (fun _ : Fin 1 => (u : ℝ)) x) :=
      hκmeas.comp (measurable_const.prodMk measurable_id)
    rw [Kernel.map_apply _ e.measurable, Kernel.withDensity_apply _ hκmeas x,
      Kernel.const_apply]
    rw [map_withDensity_of_measurePreserving_equiv e volume volume
      (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)) _
      hslice]
    rw [conditionedPastStateKernel, Kernel.withDensity_apply _
      (measurable_conditionedPastStateKernel_density _ _ _) x, Kernel.const_apply]
    congr 1
    funext y
    simp [conditionedPositiveFutureVectorDensity, conditionedPositiveTimeChainDensity,
      List.ofFn_succ, e]
  have hm : Measurable (fun p : BrownianPath =>
      ((fun i => -(p (ss i))), (fun _ : Fin 1 => -(p u)))) :=
    (measurable_pi_iff.mpr fun i => (ContinuousMap.measurable_eval _).neg).prodMk
      (measurable_pi_iff.mpr fun _ => (ContinuousMap.measurable_eval _).neg)
  have ht : Measurable (Prod.map (id : (Fin (k+1) → ℝ) → _) e) :=
    measurable_id.prodMap e.measurable
  calc
    _ = (P.map (fun p : BrownianPath =>
        ((fun i => -(p (ss i))), (fun _ : Fin 1 => -(p u))))).map (Prod.map id e) := by
      rw [Measure.map_map ht hm]
      rfl
    _ = (((volume : Measure (Fin (k+1) → ℝ)).withDensity
        (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))) ⊗ₘ κ).map
        (Prod.map id e) := by rw [(negativeConditionedLaw_finitePastFuture_compProd hP ss future hs (fun _ => ((hs (Fin.last k)).trans (NNReal.coe_lt_coe.mpr hu))) (strictMono_finAppend_of_cross ss future hmono (Subsingleton.strictMono future) (fun i _ => (hmono.monotone (Fin.le_last i)).trans_lt hu)))]
    _ = _ := by rw [← Measure.compProd_map e.measurable, hmapKernel]

end DOZZ.Proofs

end
