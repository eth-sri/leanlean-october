/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ExtendedSeibergN

/-! Strict parameter neighborhoods for the finite-insertion extended Seiberg domain. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- The background charge varies continuously away from zero. -/
theorem continuousAt_Q {γ : ℝ} (hγ : γ ≠ 0) : ContinuousAt Q γ := by
  unfold Q
  fun_prop
section
variable {N : ℕ} (q : ℝ × (Fin N → ℝ))

/-- The finite-insertion zero-mode exponent varies jointly continuously away from zero. -/
theorem continuousAt_nPointSExp (hq : q.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × (Fin N → ℝ) => nPointSExp p.1 p.2) q := by
  have hs : ContinuousAt (fun p => ∑ i, p.2 i) q := by fun_prop
  exact (hs.sub (continuousAt_const.mul
    ((continuousAt_Q hq).comp continuousAt_fst))).div continuousAt_fst hq

/-- All strict admissibility inequalities persist on a joint parameter neighborhood. -/
theorem extendedSeibergN_mem_nhds (hq : 0 < q.1) (hq2 : q.1 < 2) (ha : ExtendedSeibergN q.1 q.2) :
    {p : ℝ × (Fin N → ℝ) | 0 < p.1 ∧ p.1 < 2 ∧ ExtendedSeibergN p.1 p.2} ∈ 𝓝 q := by
  have hQ := (continuousAt_Q hq.ne').comp continuousAt_fst
  have hs := (continuousAt_nPointSExp q hq.ne').neg
  have hb : ContinuousAt (fun p => 4 / p.1 ^ 2) q :=
    continuousAt_const.div (continuousAt_fst.pow 2) (pow_ne_zero _ hq.ne')
  have hc : ∀ i, ContinuousAt (fun p => p.2 i) q :=
    fun i => (continuous_apply i).continuousAt.comp continuousAt_snd
  have hi : ∀ i, ContinuousAt
      (fun p => 2 / p.1 * (Q p.1 - p.2 i)) q :=
    fun i => (continuousAt_const.div continuousAt_fst hq.ne').mul (hQ.sub (hc i))
  have hroot : ∀ᶠ p in 𝓝 q, ∀ i, p.2 i < Q p.1 := by
    rw [Filter.eventually_all]
    exact fun i => (hc i).eventually_lt hQ (ha.1 i)
  have hinsert : ∀ᶠ p in 𝓝 q, ∀ i, -nPointSExp p.1 p.2 <
      2 / p.1 * (Q p.1 - p.2 i) := by
    rw [Filter.eventually_all]
    exact fun i => hs.eventually_lt (hi i) (ha.2.2 i)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hq,
    continuousAt_fst.eventually_lt continuousAt_const hq2,
    hroot, hs.eventually_lt hb ha.2.1, hinsert] with p hp hp2 hr hbulk hins
  tauto

end

end DOZZ.Proofs
