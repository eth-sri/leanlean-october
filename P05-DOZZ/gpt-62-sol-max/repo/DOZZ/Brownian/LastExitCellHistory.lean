/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitHistoryAvoidanceFactorization
public import DOZZ.Brownian.LastExitDyadicCells
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Last-exit cell history events

The event that the path visits the barrier on a compact deterministic interval is measurable
with respect to the raw history at its right endpoint. This makes the deterministic-time
avoidance factorization applicable to dyadic last-exit cells.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- A positive conditioned path visits `c` in the closed interval `[a,b]`. -/
def conditionedPositiveHistoryHitsOnInterval (a b c : ℝ≥0) : Set BrownianPath :=
  {p | ∃ u : ℝ≥0, a ≤ u ∧ u ≤ b ∧ conditionedPositiveStateAt u p = c}

/-- A compact-interval barrier hit is determined measurably by the history through its right
endpoint. -/
theorem measurableSet_conditionedPositiveHistoryHitsOnInterval
    (a b c : ℝ≥0) :
    MeasurableSet[conditionedPositiveNaturalFiltration b]
      (conditionedPositiveHistoryHitsOnInterval a b c) := by
  let K := {u : ℝ // (a : ℝ) ≤ u ∧ u ≤ (b : ℝ)}
  let τ : K → ℝ≥0 := fun u => ⟨u.1, le_trans a.property u.2.1⟩
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp
      (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ)))
  let : MeasurableSpace BrownianPath := conditionedPositiveNaturalFiltration b
  have hτ : Continuous τ :=
    Continuous.subtype_mk continuous_subtype_val (fun u => le_trans a.property u.2.1)
  let segment : BrownianPath → C(K, ℝ) := fun p =>
    ⟨fun u => conditionedPositiveStateAt (τ u) p,
      (p.continuous.neg).comp hτ⟩
  let H : Set C(K, ℝ) := {f | ∃ u : K, f u = (c : ℝ)}
  let V : Set C(K, ℝ) := {f | MapsTo f Set.univ ({(c : ℝ)}ᶜ)}
  have hV : IsOpen V := by
    exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (isOpen_compl_iff.mpr isClosed_singleton)
  have hHV : H = Vᶜ := by
    ext f
    simp [H, V, MapsTo, Set.mem_compl_iff]
  have hHclosed : IsClosed H := hHV ▸ hV.isClosed_compl
  have hsegment : Measurable segment := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro u
    change Measurable[conditionedPositiveNaturalFiltration b]
      (conditionedPositiveStateAt (τ u))
    apply Measurable.of_comap_le
    have hub : τ u ≤ b := by
      apply NNReal.coe_le_coe.mp
      exact u.2.2
    exact le_iSup_of_le (τ u) (le_iSup_of_le hub le_rfl)
  have hpre : conditionedPositiveHistoryHitsOnInterval a b c = segment ⁻¹' H := by
    ext p
    constructor
    · rintro ⟨u, hau, hub, hval⟩
      exact Exists.intro ⟨↑u, ⟨cast (Eq.symm NNReal.coe_le_coe._simp_1) hau, cast (Eq.symm NNReal.coe_le_coe._simp_1) hub⟩⟩ hval
    · rintro ⟨u, hval⟩
      exact Exists.intro (τ u) ⟨NNReal.coe_le_coe.mp u.property.left, ⟨NNReal.coe_le_coe.mp u.property.right, hval⟩⟩
  rw [hpre]
  exact hHclosed.measurableSet.preimage hsegment

end DOZZ.Proofs

end
