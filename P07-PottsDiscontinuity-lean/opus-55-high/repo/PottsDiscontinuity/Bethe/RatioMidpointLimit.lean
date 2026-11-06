module

public import PottsDiscontinuity.Bethe.RatioDensityLimits
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

theorem ratio_source_midpoint_limit {Δ c : ℝ} (hΔ : Δ < -1) (hc : 2 < c)
    (s : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hN : ∀ i, 0 < N i)
    (p : ∀ i, Fin (N i / 2) → ℝ) (hp : ∀ i, p i ∈ S_n (N i / 2))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by grind) (by omega)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by grind) (by omega) x - rho Δ x) (hb i)) atTop (𝓝 0)) :
    Tendsto (fun i => Real.exp (∑ j : Fin (N i / 4 - s - 1), ratioMidpointLog c (N i) (h4 i) (p i) s j))
      atTop (𝓝 (2 / Real.pi)) := by
  let t := fun i => N i / 4 - s - 1
  let v := fun i k =>
    if hk : k < t i then ratioMidpointLog c (N i) (h4 i) (p i) s ⟨k, hk⟩ else 0
  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  obtain ⟨mρ, hmρ, hmesh⟩ := eventually_rootPartition_gap_le hΔ 0 N (fun i => N i / 2)
    p hp hnP (fun i => by omega) (by grind) hb hlim
  let D := 2 / mρ
  have hmeshD : ∀ᶠ i in atTop, ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (hnP i) j.succ -
        rootPartitionPoint (N i / 2) (p i) (hnP i) j.castSucc ≤ D / N i := by
    filter_upwards [hmesh] with i hi j
    apply (hi j).trans_eq
    ring
  obtain ⟨M, hM, hupper⟩ := ratio_density_eventually_bounded hΔ
    (fun i => rootStepDensity (N i) (N i / 2) (p i) (hp i) (hnP i) (by omega)) hb hlim
  obtain ⟨B, hB, hprofile⟩ := ratio_midpoint_log_bound hc
  let C := B * (2 * M * D) ^ 2
  have hbound : ∀ᶠ i in atTop, ∀ k, ‖v i k‖ ≤ C / ((k : ℝ) + 1) ^ 2 := by
    filter_upwards [hmeshD, hupper] with i hiMesh hiUpper k
    by_cases hk : k < t i
    · rw [show v i k = _ from dite_eq_left hk, Real.norm_eq_abs]
      have : k + 1 < N i / 4 := by simp only [t] at hk; omega
      exact ratio_midpoint_rank_bound hB hM (by positivity) (hN i) (ratio_positiveRoot_pos (h4 i) (hp i) ⟨k, by omega⟩)
        ((hp i).2.1.monotone (by grind)) (ratio_positiveRoot_mem_Ioo (h4 i) (hp i) ⟨k + 1, this⟩).2 hprofile
        (root_interior_gap_of_mesh (p i) (hnP i) hiMesh (N i / 4 + k) (by grind)) (ratio_positiveRoot_lower (h4 i) (hp i) (hnP i) hiUpper ⟨k, by omega⟩)
    · rw [show v i k = 0 from dite_eq_right hk, norm_zero]
      positivity
  have hpoint (k : ℕ) : Tendsto (fun i => v i k) atTop (𝓝 (Real.log (ratioWallisFactor k))) := by
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp (hNlim.eventually (eventually_ge_atTop (((4 * (k + s + 2) : ℕ) : ℝ))))
    have hk (i : ℕ) : 4 * (k + s + 2) ≤ N (i + i₀) := by exact_mod_cast hi₀ _ (by omega)
    have hT := tendsto_add_atTop_nat i₀
    have hX := ratio_full_positive_rank_scaling hΔ (fun i => N (i + i₀)) (fun i => h4 _) (fun i => hN _)
      (fun i => p _) (fun i => hp _) (hNlim.comp hT) (fun i => hb _) (hlim.comp hT)
    rw [← tendsto_add_atTop_iff_nat i₀]
    refine (ratio_half_integer_midpoint_log_tendsto hc (rho_pos hΔ 0) k (fun i => (N (i + i₀) : ℝ)) (fun i => by exact_mod_cast (hN _).ne')
      (hNlim.comp hT) _ _ (fun i => ratio_positiveRoot_mem_Ioo (h4 _) (hp _) _)
      (fun i => ratio_positiveRoot_mem_Ioo (h4 _) (hp _) _) (fun i => ratio_positiveRoot_pos (h4 _) (hp _) _)
      (fun i => ratio_positiveRoot_pos (h4 _) (hp _) _) (hX k fun i => by grind [hk i])
      (by convert hX (k + 1) (fun i => by grind [hk i]) using 3; push_cast; ring)).congr fun i => (dite_eq_left (by simp only [t]; have := hk i; omega)).symm
  refine (ratio_wallis_limit_of_log_bounds t v C hpoint (fun i k hk => dite_eq_right (not_lt.mpr hk)) hbound).congr fun i => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  exact congrArg _ (sum_congr rfl fun j _ => dite_eq_left j.isLt)

end PottsDiscontinuity.Bethe
