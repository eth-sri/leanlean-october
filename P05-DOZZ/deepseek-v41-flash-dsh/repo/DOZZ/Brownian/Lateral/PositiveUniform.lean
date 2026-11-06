/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.UpperConditionedBlocks

/-!
# Uniform positive half-cylinder moments

Compact charge and positive-drift ranges give one below-one normalization bound and one
Brownian increment exponential bound. The resulting geometric block sequence and its positive
roots are summable with common constants. Infinite Minkowski transfers a uniform moment of the
given lateral unit interval to the entire upper-conditioned half-cylinder. The enclosing-order
lemma keeps the full strict subcritical margin needed by the proof of the reflection
statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Compact positive drift ranges have a common positive lower endpoint and finite upper
endpoint, without prescribing a particular normalization of the parameter set. -/
theorem conditioned_compact_positive_drift_bounds
    (Kν : Set ℝ) (hKν : IsCompact Kν) (hne : Kν.Nonempty)
    (hν : ∀ ν ∈ Kν, 0 < ν) :
    ∃ ν₀ N : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Kν, ν₀ ≤ ν ∧ ν ≤ N := by
  obtain ⟨ν₀, hlo, hmin⟩ := hKν.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨N, hhi, hmax⟩ := hKν.exists_isMaxOn hne continuous_id.continuousOn
  exact ⟨ν₀, N, hν ν₀ hlo, fun ν h => ⟨hmin h, hmax h⟩⟩

/-- Inserting orders zero and one before taking compact extrema gives a negative lower
endpoint and an upper endpoint above one, while preserving strict subcritical slack. This
lets the two-sided assembly use inverse bounds and infinite Minkowski at the same endpoints. -/
theorem lateralGMC_compact_moment_endpoints_across_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (hγne : Kγ.Nonempty) (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ l u δ : ℝ, l < 0 ∧ 1 < u ∧ 0 < δ ∧
      (∀ q ∈ Kq, l < q ∧ q < u) ∧ (∀ γ ∈ Kγ, u + δ ≤ 4 / γ ^ 2) := by
  let K := Kq ∪ ({0, 1} : Set ℝ)
  have hK : IsCompact K := hKq.union (Set.toFinite _).isCompact
  have h0 : (0 : ℝ) ∈ K := Or.inr (by simp)
  have hsub : ∀ γ ∈ Kγ, ∀ q ∈ K, q < 4 / γ ^ 2 := by
    intro γ hγ q hqm
    have hγp := (hZ γ hγ).1
    have hγhi := (hZ γ hγ).2.1
    have hs : 0 < γ ^ 2 := sq_pos_of_pos hγp
    rcases hqm with hqm | hqm
    · exact hq γ hγ q hqm
    · have hq01 : q = 0 ∨ q = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hqm
      rcases hq01 with rfl | rfl
      · exact div_pos (by norm_num) hs
      · apply (lt_div_iff₀ hs).mpr
        nlinarith
  obtain ⟨l, u, δ, hδ, hend, hmargin⟩ := lateralGMC_compact_moment_endpoints
    Kγ K hKγ hK hγne ⟨0, h0⟩ (fun γ hγ => (hZ γ hγ).1) hsub
  exact ⟨l, u, δ, (hend 0 h0).1, (hend 1 (Or.inr (by simp))).2, hδ,
    fun q hqm => hend q (Or.inl hqm), hmargin⟩

end DOZZ.Proofs
