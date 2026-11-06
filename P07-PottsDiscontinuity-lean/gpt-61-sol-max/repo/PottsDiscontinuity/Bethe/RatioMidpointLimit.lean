module
public import Mathlib

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
  let x := ratioPositiveRoot N h4 p ⟨j.val, by  omega⟩
  let y := ratioPositiveRoot N h4 p ⟨j.val + 1, by  omega⟩
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
  let v  := fun i k =>
    if hk : k < t i then ratioMidpointLog c (N i) (h4 i) (p i) s ⟨k, hk⟩ else 0
  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  
  obtain ⟨mρ, hmρ, hmesh⟩ := eventually_rootPartition_gap_le hΔ 0 N (fun i => N i / 2)
    p hp hnP  fun i => by omega   fun i => by grind  hb hlim
  let D := 2 / mρ
  have hD : 0 ≤ D := by
                       bound
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
  have hbound : ∀ᶠ i in atTop, ∀ k, ‖v i k‖ ≤ C / ( k  + 1) ^ 2 := by
    filter_upwards [hmeshD, hupper] with i hiMesh hiUpper k
    by_cases hk : k < t i
    · let j : Fin (N i / 4) := ⟨k, by dsimp [t] at hk; omega⟩
      
      
      
      
      have hbpi := (ratio_positiveRoot_mem_Ioo (h4 i) (hp i) (⟨k + 1, by dsimp [t] at hk; omega⟩)).2
      
      
      
      have hh := ratio_midpoint_rank_bound hB hM hD (hN i) (ratio_positiveRoot_pos (h4 i) (hp i) j) ((hp i).2.1.monotone (by aesop)) hbpi hprofile (by
                                                                                   
                                                                                   exact (root_interior_gap_of_mesh (p i) (hnP i) hiMesh (N i / 4 + k)
                                                                                            (by grind))) (ratio_positiveRoot_lower (h4 i) (hp i) (hnP i) hiUpper j)
      
      rw [show v i k = ratioMidpointLog c (N i) (h4 i) (p i) s ⟨k, hk⟩ from dite_eq_left hk,
        Real.norm_eq_abs]
      exact hh
    · rw [show v i k = 0 from dite_eq_right hk, norm_zero]
      exact div_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _)
  have hpoint (k : ℕ) : Tendsto (fun i => v i k) atTop (𝓝 (Real.log (ratioWallisFactor k))) := by
    have hlarge : ∀ᶠ i in atTop, k < t i := by
      filter_upwards [hNlim.eventually (eventually_ge_atTop  ((4 * (k + s + 2) ) : ℝ) )] with i hi
      have hnat : 4 * (k + s + 2) ≤ N i := by exact_mod_cast hi
      dsimp [t]
      
      omega
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hlarge
    let T := fun i  => i₀ + i
    have hT : Tendsto T atTop atTop := tendsto_atTop.mpr  fun a => eventually_atTop.mpr
      ⟨a, fun b hb => by dsimp [T]; omega⟩ 
    have hkT (i : ℕ)  := hi₀ (T i) (by dsimp [T]; omega)
    have hkX (i : ℕ) : k < N (T i) / 4 := by have := hkT i; dsimp [t] at this; omega
    have hkY (i : ℕ) : k + 1 < N (T i) / 4 := by have := hkT i; dsimp [t] at this; omega
    
    
    
    
    
    have ht := ratio_half_integer_midpoint_log_tendsto hc (rho_pos hΔ 0) k
      (fun i =>  N (T i) ) (fun i => by exact_mod_cast (hN (T i)).ne') (hNlim.comp hT) (fun i => ratioPositiveRoot (N (T i)) (h4 (T i)) (p (T i)) ⟨k, hkX i⟩) (fun i => ratioPositiveRoot (N (T i)) (h4 (T i)) (p (T i)) ⟨k + 1, hkY i⟩)
      (fun i => ratio_positiveRoot_mem_Ioo (h4 (T i)) (hp (T i)) _)
      (fun i => ratio_positiveRoot_mem_Ioo (h4 (T i)) (hp (T i)) _)
      (fun i => ratio_positiveRoot_pos (h4 (T i)) (hp (T i)) _)
      (fun i => ratio_positiveRoot_pos (h4 (T i)) (hp (T i)) _) (ratio_full_positive_rank_scaling hΔ (fun i => N (T i)) (fun i => h4 (T i))
                                                                   (fun i => hN (T i)) (fun i => p (T i)) (fun i => hp (T i)) (hNlim.comp hT)
                                                                   (fun i => hb (T i)) (hlim.comp hT) k hkX) (by
                                                                      convert (ratio_full_positive_rank_scaling hΔ (fun i => N (T i)) (fun i => h4 (T i))
                                                                                 (fun i => hN (T i)) (fun i => p (T i)) (fun i => hp (T i)) (hNlim.comp hT)
                                                                                 (fun i => hb (T i)) (hlim.comp hT) (k + 1) hkY) using 1
                                                                      push_cast
                                                                      ring)
    have hvTail : Tendsto (fun i => v (T i) k) atTop (𝓝 (Real.log (ratioWallisFactor k))) := by
      aesop  (add norm (by omega))  (add simp [ratioMidpointLog])  (add unsafe apply [_root_.congrArg])
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hvTail ε hε)
    apply eventually_atTop.mpr
    refine ⟨i₀ + j₀, ?_⟩
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
    exact hj₀ j (by omega)
  
  have hsum (i : ℕ) :  ∑ k ∈ range (t i), v i k  =
      ∑ j : Fin (N i / 4 - s - 1), ratioMidpointLog c (N i) (h4 i) (p i) s j := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro j hj
    exact dite_eq_left j.isLt
  simpa only [hsum] using  ratio_wallis_limit_of_log_bounds t v C hpoint
                             (fun i k hk => dite_eq_right (not_lt.mpr hk)) hbound 

end PottsDiscontinuity.Bethe
