/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianLaw
public import DOZZ.Brownian.LastExitAvoidanceChain

/-!
# Positive-coordinate factorization of conditioned entrance FDDs

The characterization `DOZZ.IsNegativeConditionedBrownianLaw` is stated for negative paths.
Reflecting every coordinate gives the positive entrance law, whose finite-dimensional density is
an entrance density followed by the positive Doob transition chain. This is the explicit density
factorization used in deterministic-time Markov calculations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- The positive conditioned transition chain over an ordered list of absolute observation times.
The initial state is observed at time `t₀`; each later factor uses the elapsed time since the
preceding observation. -/
noncomputable def conditionedPositiveTimeChainDensity (ν t₀ x₀ : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveTransitionDensity ν (t - t₀) x₀ x *
        conditionedPositiveTimeChainDensity ν t x ts xs
  | _, _ => 0
termination_by times _ => times.length

/-- The positive-coordinate form of the entrance finite-dimensional density. -/
noncomputable def conditionedPositiveFDDDensity (ν : ℝ) : List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveEntranceDensity ν t x *
        conditionedPositiveTimeChainDensity ν t x ts xs
  | _, _ => 0

/-- Reflecting the state and every later coordinate in the negative transition chain gives
exactly the positive Doob transition chain. -/
theorem negativeConditionedTransitionChainDensity_reflect
    (ν t x : ℝ) (times values : List ℝ) :
    negativeConditionedTransitionChainDensity ν t (-x) times (values.map fun y => -y) =
      conditionedPositiveTimeChainDensity ν t x times values := by
  induction times generalizing t x values with
  | nil =>
      cases values <;>
        simp [negativeConditionedTransitionChainDensity,
          conditionedPositiveTimeChainDensity]
  | cons s ss ih =>
      cases values with
      | nil =>
          simp [negativeConditionedTransitionChainDensity,
            conditionedPositiveTimeChainDensity]
      | cons y ys =>
          simp [negativeConditionedTransitionChainDensity,
            conditionedPositiveTimeChainDensity, negativeConditionedTransitionDensity, ih]

/-- The negative entrance density, after reflecting its coordinates, is the explicit
positive entrance density and transition chain. -/
theorem negativeConditionedFDDDensity_reflect
    (ν : ℝ) (times values : List ℝ) :
    negativeConditionedFDDDensity ν times (values.map fun y => -y) =
      conditionedPositiveFDDDensity ν times values := by
  cases times with
  | nil =>
      cases values <;>
        simp [negativeConditionedFDDDensity, conditionedPositiveFDDDensity]
  | cons t ts =>
      cases values with
      | nil =>
          simp [negativeConditionedFDDDensity, conditionedPositiveFDDDensity]
      | cons x xs =>
          simp only [negativeConditionedFDDDensity, conditionedPositiveFDDDensity,
            List.map_cons]
          rw [negativeConditionedTransitionChainDensity_reflect]
          simp

/-- The positive finite-dimensional density factors at its first observation into the entrance
density and the successive transition densities. -/
theorem conditionedPositiveFDDDensity_cons
    (ν t x : ℝ) (times values : List ℝ) :
    conditionedPositiveFDDDensity ν (t :: times) (x :: values) =
      conditionedPositiveEntranceDensity ν t x *
        conditionedPositiveTimeChainDensity ν t x times values := by
  rfl

/-- The final observation time after appending a finite ordered history to a starting time. -/
def conditionedPositiveLastTime (t₀ : ℝ) : List ℝ → ℝ
  | [] => t₀
  | t :: ts => conditionedPositiveLastTime t ts

/-- The final state after appending a finite state history to a starting state. -/
def conditionedPositiveLastState (x₀ : ℝ) : List ℝ → ℝ
  | [] => x₀
  | x :: xs => conditionedPositiveLastState x xs
section
variable (ν t₀ x₀ : ℝ) (pastTimes pastValues futureTimes futureValues : List ℝ)
section
variable (hpast : pastTimes.length = pastValues.length)
include hpast

/-- The absolute-time transition density factors at the final state of a finite past list. -/
theorem conditionedPositiveTimeChainDensity_append
    :
    conditionedPositiveTimeChainDensity ν t₀ x₀
        (pastTimes ++ futureTimes) (pastValues ++ futureValues) =
      conditionedPositiveTimeChainDensity ν t₀ x₀ pastTimes pastValues *
        conditionedPositiveTimeChainDensity ν
          (conditionedPositiveLastTime t₀ pastTimes)
          (conditionedPositiveLastState x₀ pastValues) futureTimes futureValues := by
  induction pastTimes generalizing t₀ x₀ pastValues with
  | nil =>
      cases pastValues with
      | nil => simp [conditionedPositiveTimeChainDensity,
          conditionedPositiveLastTime, conditionedPositiveLastState]
      | cons x xs => simp at hpast
  | cons t ts ih =>
      cases pastValues with
      | nil => simp at hpast
      | cons x xs =>
          have htail : ts.length = xs.length := by simp_all
          simp only [List.cons_append, conditionedPositiveTimeChainDensity,
            conditionedPositiveLastTime, conditionedPositiveLastState]
          rw [ih t x xs htail]
          ring

/-- The explicit entrance FDD density splits at the state reached after any finite ordered past.
The right factor is exactly the finite transition density started at that deterministic state. -/
theorem conditionedPositiveFDDDensity_split
    :
    conditionedPositiveFDDDensity ν (t₀ :: (pastTimes ++ futureTimes))
        (x₀ :: (pastValues ++ futureValues)) =
      (conditionedPositiveEntranceDensity ν t₀ x₀ *
        conditionedPositiveTimeChainDensity ν t₀ x₀ pastTimes pastValues) *
        conditionedPositiveTimeChainDensity ν
          (conditionedPositiveLastTime t₀ pastTimes)
          (conditionedPositiveLastState x₀ pastValues) futureTimes futureValues := by
  rw [conditionedPositiveFDDDensity_cons,
    conditionedPositiveTimeChainDensity_append ν t₀ x₀ pastTimes pastValues
      futureTimes futureValues hpast]
  ring

end

end


end DOZZ.Proofs

end
