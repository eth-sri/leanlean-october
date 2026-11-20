module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Strongly continuous semigroups -/

open Filter Topology Set

variable (𝕜 X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The semigroup laws and strong continuity at time zero. -/
structure C0Semigroup where
  T : ℝ → X →L[𝕜] X
  T_zero : T 0 = ContinuousLinearMap.id 𝕜 X
  T_add : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s)
  T_cont : ∀ y : X, Tendsto (fun t => T t y) (𝓝[≥] 0) (𝓝 y)

namespace C0Semigroup

/-- A sufficiently short time window can be placed around any nonnegative time,
starting at a nonnegative time (possibly zero). -/
lemma exists_window {t δ : ℝ} (hδ : 0 < δ) :
    ∃ a ≥ 0, ∀ᶠ s in 𝓝[Ici 0] t, s - a ∈ Ico 0 δ := by
  let a := max 0 (t - δ / 2)
  refine ⟨a, le_max_left _ _, eventually_nhdsWithin_iff.2 ?_⟩
  filter_upwards [Ioo_mem_nhds (show t - δ / 2 < t by linarith) (show t < t + δ / 2 by linarith)]
    with s hs h0
  grind

variable {𝕜 X} [CompleteSpace X] (S : C0Semigroup 𝕜 X)

/-- The operator norms are bounded on a short initial interval, by Banach–Steinhaus. -/
private theorem exists_bound_near_zero :
    ∃ δ > 0, ∃ M, ∀ t ∈ Ico 0 δ, ‖S.T t‖ ≤ M := by
  by_contra! h
  choose t ht hb using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity) n
  have hl : Tendsto t atTop (𝓝[≥] 0) := tendsto_nhdsWithin_iff.2
    ⟨squeeze_zero (fun n => (ht n).1) (fun n => (ht n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat,
      .of_forall fun n => (ht n).1⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => S.T (t n)) fun x => by
    simpa only [isBounded_iff_forall_norm_le, forall_mem_range, Function.comp_apply] using
      Metric.isBounded_range_of_tendsto _ ((S.T_cont x).comp hl)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact hn.not_ge ((hb n).le.trans (hC n))

/-- **Proposition 1.2**: every semigroup orbit is continuous on the half-line. -/
theorem continuousOn_orbit (y : X) : ContinuousOn (fun t => S.T t y) (Ici 0) := by
  obtain ⟨δ, hδ, M, hb⟩ := S.exists_bound_near_zero
  have local_cont (z : X) : ContinuousOn (fun t => S.T t z) (Ico 0 δ) := by
    apply UniformContinuousOn.continuousOn
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    have H : Tendsto (fun r => M * dist (S.T r z) z) (𝓝[≥] 0) (𝓝 0) := by
      simpa using ((S.T_cont z).dist (tendsto_const_nhds (x := z))).const_mul M
    obtain ⟨η, hη, hc⟩ := (nhdsGE_basis_Ico (0 : ℝ)).mem_iff.1 (H.eventually_lt_const hε)
    refine ⟨η, hη, fun s hs t ht hd => ?_⟩
    wlog h : t ≤ s generalizing s t
    · rw [dist_comm]
      exact this t ht s hs (dist_comm s t ▸ hd) (le_of_not_ge h)
    have h0 := sub_nonneg.mpr h
    have he : S.T s z = S.T t (S.T (s - t) z) := by
      rw [← ContinuousLinearMap.comp_apply, ← S.T_add _ _ ht.1 h0, add_sub_cancel]
    rw [he, dist_eq_norm, ← map_sub]
    apply ((S.T t).le_of_opNorm_le (hb t ht) _).trans_lt
    rw [← dist_eq_norm]
    exact hc ⟨h0, by simpa [Real.dist_eq, abs_of_nonneg h0] using hd⟩
  intro t ht
  obtain ⟨a, ha, hw⟩ := exists_window (t := t) hδ
  refine ((local_cont (S.T a y)) _ (hw.self_of_nhdsWithin ht)).comp_of_preimage_mem_nhdsWithin
    (f := fun s => s - a) (continuous_sub_right a).continuousWithinAt hw |>.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [hw] with s hs
  rw [Function.comp_apply, ← ContinuousLinearMap.comp_apply, ← S.T_add _ _ hs.1 ha, sub_add_cancel]

end C0Semigroup
