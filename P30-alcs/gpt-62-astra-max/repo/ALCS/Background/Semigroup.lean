module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

public section
open Filter Topology Set

namespace PalomarALCS
-- Right-hand neighbourhood filter, including zero.
scoped notation "𝓝₊" => 𝓝[≥] (0 : ℝ)

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {T : ℝ → X →L[𝕜] X} (cont : ∀ x, Tendsto (fun t => T t x) 𝓝₊ (𝓝 x))
include cont

private lemma bound : ∃ K : ℝ, ∀ᶠ t in 𝓝₊, ‖T t‖ ≤ K := by
  by_contra! h
  obtain ⟨B, hB⟩ := 𝓝₊.exists_antitone_basis
  choose t hb ht using fun n : ℕ => ((h n).and_eventually (hB.mem n)).exists
  obtain ⟨K, hK⟩ := banach_steinhaus (g := fun n => T (t n)) fun x => by
    simpa [bddAbove_def] using ((cont x).comp (hB.tendsto ht)).norm.bddAbove_range
  obtain ⟨n, hn⟩ := exists_nat_gt K
  linarith [hK n, hb n]

/-- A curve uniformly approximated on short intervals by free evolution from
its left endpoint is continuous. Taking the error to be zero gives continuity
of ordinary semigroup orbits. -/
theorem continuous_approx (F : ℝ → X) {w : ℝ → ℝ} (hw : Tendsto w 𝓝₊ (𝓝 0))
    (err : ∀ a ≥ 0, ∀ r ≥ 0, dist (T r (F a)) (F (a + r)) ≤ w r) : ContinuousOn F (Ici 0) := by
  obtain ⟨K, hK⟩ := bound cont
  rw [Metric.continuousOn_iff]; intro x hx ε hε
  obtain ⟨d, hd, h⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (hK.and (hw.eventually_lt_const (show 0 < ε / 3 by positivity)))
  -- Start a little before x, or at zero if x is near the endpoint.
  set a := max 0 (x - d) with eq
  have ha : 0 ≤ a := le_max_left ..
  have right := (cont (F a)).congr_dist (squeeze_zero'
    (.of_forall fun _ => dist_nonneg) (Eventually.mono self_mem_nhdsWithin fun _ ht => err a ha _ ht) hw)
  obtain ⟨η, hη, hs⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (((tendsto_iff_dist_tendsto_zero.mp right).const_mul K).eventually_lt_const
      (show K * 0 < ε / 3 by linarith))
  -- Propagate the small right increment at a forward by a common time b.
  have pair (r b : ℝ) (hr : r ∈ Icc 0 η) (hb : b ∈ Icc 0 d) : dist (F (a + r + b)) (F (a + b)) < ε := by
    grw [dist_triangle4_left (T b (F (a + r))) (T b (F a)), ContinuousLinearMap.dist_le_opNorm,
      (h hb).1, err _ (add_nonneg ha hr.1) _ hb.1, err _ ha _ hb.1]
    have := hs hr; have := h hb; grind
  refine ⟨min d η, lt_min hd hη, fun t ht near => ?_⟩
  simp only [Real.dist_eq, lt_min_iff, abs_lt] at near
  -- Use the same estimate on either side of x.
  have H := pair (t - x) (x - a); have H' := pair (x - t) (t - a)
  ring_nf at H H'; grind [dist_comm]

/-- Proposition 1.2: exact free evolution has zero error. -/
theorem continuousOn_orbit (add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = (T a).comp (T b))
    (y : X) : ContinuousOn (fun t => T t y) (Ici 0) := by
  apply continuous_approx cont _ (w := 0) tendsto_const_nhds
  intro a ha r hr; simp [add_comm a, add r a hr ha]

end PalomarALCS
