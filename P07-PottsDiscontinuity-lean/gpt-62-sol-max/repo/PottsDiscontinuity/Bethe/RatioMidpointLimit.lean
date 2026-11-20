module

public import PottsDiscontinuity.Bethe.RatioMidpointBounds
public import PottsDiscontinuity.Bethe.RatioMidpointPointwise
public import PottsDiscontinuity.Bethe.RatioPositiveRoots

/-! # The source odd midpoint product tends to 2/π

The zero midpoint is omitted. The remaining positive and negative
midpoints pair into the squared factors represented by these logarithms.
-/

@[expose] public section

open Set Filter Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

/-- The logarithm of a paired positive/negative midpoint factor. -/
noncomputable def ratioMidpointLog (c : ℝ) (N : ℕ) (h4 : 4 ∣ N)
    (p : Fin (N / 2) → ℝ) (s : ℕ) (j : Fin (N / 4 - s - 1)) : ℝ :=
  let x := ratioPositiveRoot N h4 p ⟨j.val, by omega⟩
  let y := ratioPositiveRoot N h4 p ⟨j.val + 1, by omega⟩
  2 * ratioEll c ((x + y) / 2) - ratioEll c x - ratioEll c y

theorem ratio_source_midpoint_limit {Δ c : ℝ} (hc : 2 < c)
    (s : ℕ) {N : ℕ → ℕ} {p : ∀ i, Fin (N i / 2) → ℝ} (R : FullRoots Δ N p) :
    Tendsto (fun i => Real.exp (∑ j : Fin (N i / 4 - s - 1), ratioMidpointLog c (N i) (R.four i) (p i) s j))
      atTop (𝓝 (2 / Real.pi)) := by
  let t (i : ℕ) := N i / 4 - s - 1
  let v (i k : ℕ) := if k < t i then
    2 * ratioEll c ((R.rank k i + R.rank (k + 1) i) / 2) -
      ratioEll c (R.rank k i) - ratioEll c (R.rank (k + 1) i) else 0
  have hD : 0 ≤ 1 / R.m := div_nonneg zero_le_one R.mpos.le
  obtain ⟨B, hB, hprofile⟩ := ratio_midpoint_log_bound hc
  let C := B * (2 * R.U * (1 / R.m)) ^ 2
  have hbound : ∀ᶠ i in atTop, ∀ k, ‖v i k‖ ≤ C / ((k : ℝ) + 1) ^ 2 := by
    filter_upwards [R.bounds] with i hi k
    by_cases hk : k < t i
    · have hk' : k + 1 < N i / 4 := by dsimp [t] at hk; omega
      have hU : 0 ≤ R.U := R.mpos.le.trans ((hi _ (Ioo_subset_Icc_self (R.rank_mem k i))).1.trans
        (hi _ (Ioo_subset_Icc_self (R.rank_mem k i))).2)
      have hab : R.rank k i ≤ R.rank (k + 1) i := by
        rw [R.rank_eq (by omega : k < N i / 4), R.rank_eq hk']
        exact (R.mem i).2.1.monotone (by simp)
      simpa [v, hk, C] using ratio_midpoint_rank_bound hB hU hD (R.pos i)
              (R.rank_pos k i) hab (R.rank_mem (k + 1) i).2 hprofile (R.rank_gap hk' fun x hx => (hi x hx).1)
              (R.rank_lower (by omega : k < N i / 4) fun x hx => (hi x hx).2)
    · simp [v, hk, C, div_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _)]
  have hpoint (k : ℕ) : Tendsto (fun i => v i k) atTop (𝓝 (Real.log (ratioWallisFactor k))) := by
    have hY : Tendsto (fun i => (N i : ℝ) * R.rank (k + 1) i) atTop
        (𝓝 (((k : ℝ) + 3 / 2) / rho Δ 0)) := by
      convert (R.rank_limits (k + 1)).2 using 2 <;> push_cast <;> ring
    refine (ratio_half_integer_midpoint_log_tendsto hc (rho_pos R.hΔ 0) k
      (fun i => (N i : ℝ)) (fun i => (Nat.cast_pos.mpr (R.pos i) : (0 : ℝ) < N i).ne') R.widthLimit
      (R.rank k) (R.rank (k + 1)) (R.rank_mem k) (R.rank_mem (k + 1))
      (R.rank_pos k) (R.rank_pos (k + 1)) (R.rank_limits k).2 hY).congr' ?_
    filter_upwards [R.eventually_rank_exists (k + s + 1)] with i hi
    have : k < t i := by dsimp [t]; omega
    simp [v, this]
  have ht := ratio_wallis_limit_of_log_bounds t v C hpoint (fun i k hk => by simp [v, not_lt.2 hk]) hbound
  refine ht.congr fun i => congrArg Real.exp ?_
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  have hj : j.val < N i / 4 - s - 1 := j.isLt
  simp [v, ratioMidpointLog, R.rank_eq (by omega : j.val < N i / 4), R.rank_eq (by omega : j.val + 1 < N i / 4)]

end PottsDiscontinuity.Bethe
