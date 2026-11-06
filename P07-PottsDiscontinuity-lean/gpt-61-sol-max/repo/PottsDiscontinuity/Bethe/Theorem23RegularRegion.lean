module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Base
public import PottsDiscontinuity.Bethe.Theorem23Dominance
public import PottsDiscontinuity.Bethe.Theorem23GapInterior
public import PottsDiscontinuity.Bethe.Theorem23Local

/-! # All zeros in the compact Bethe region are interior and regular -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem abs_compact_inverse_parameter_lt_one {Δ₀ ε : ℝ} (hΔ₀ : Δ₀ < -1)
    (hε : ε ∈ Icc (1 / Δ₀) 0) : |ε| < 1 := by
  have h0 := abs_lt.mp (abs_inverse_parameter_lt_one hΔ₀)
  grind

theorem inverse_parameter_le_cutoff {Δ₀ ε : ℝ} (_hΔ₀ : Δ₀ < -1)
    (hε : ε ∈ Icc (1 / Δ₀) 0) (hne : ε ≠ 0) : 1 / ε ≤ Δ₀ := by
  
  have h := one_div_le_one_div_of_neg_of_le (lt_of_le_of_ne hε.2 hne) hε.1
  simp_all

/-- Uniform compact-region data for the continuation theorem. Every zero in
the region is strictly interior and has invertible state derivative, including
the base parameter epsilon=0. -/
theorem exists_uniform_regular_Bethe_region (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ c D K : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      8 * Real.pi * (2 * r + 1 : ℝ) < D ∧ 0 < K ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N k : ℕ), N₀ ≤ N → N = 2 * ( k + 1  + r) →
      ∀ hs : 2 * (k + 1) ≤ N,
      discreteBaseCoordinates N (k + 1) ∈ interior (betheGapRegion k (c / N) (D / N)) ∧
      (∀ ε ∈ Icc (1 / Δ₀) 0, ∀ q ∈ betheGapRegion k (c / N) (D / N),
        discreteCoordinateResidualInv ε N (k + 1) q = 0 →
        q ∈ interior (betheGapRegion k (c / N) (D / N)) ∧
        ∃ e : (Fin ((k + 1) / 2) → ℝ) ≃L[ℝ]  Fin ((k + 1) / 2) → ℝ ,
          (fderiv ℝ (fun z : ℝ × (Fin ((k + 1) / 2) → ℝ) =>
            discreteCoordinateResidualInv z.1 N (k + 1) z.2) (ε, q)).comp
              (ContinuousLinearMap.inr ℝ ℝ (Fin ((k + 1) / 2) → ℝ)) =
            (e : (Fin ((k + 1) / 2) → ℝ) →L[ℝ]  Fin ((k + 1) / 2) → ℝ )) ∧
       ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀) (q : Fin ((k + 1) / 2) → ℝ)
        (_hq : q ∈ betheGapRegion k (c / N) (D / N)),
        DiscreteBetheEquation Δ N (k + 1) (discreteSymLift (k + 1) q) →
        ∀ hp : discreteSymLift (k + 1) q ∈ S_n (k + 1),
        densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
          (fun x => rootStepDensity N (k + 1) (discreteSymLift (k + 1) q) hp (by omega) hs x - rho Δ x)
          (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) _ hp (by omega) hs) ≤ K / N  := by
  obtain ⟨c, D, K, hc, hcpi, hDlarge, hK, M₀, hM₀, hbootstrap⟩ :=
    exists_uniform_strict_gap_bootstrap r hΔ₀
  
  obtain ⟨L₀, hL₀, hmatrix⟩ := exists_uniform_Bethe_matrix_nonsingular hΔ₀ D (lt_trans (by positivity) hDlarge).le
  refine ⟨c, D, K, hc, hcpi, hDlarge, hK, max M₀ L₀,
    lt_of_lt_of_le hM₀ (le_max_left _ _), fun N k hlarge hcount hs => ?_⟩
  have hMlarge  := (le_max_left _ _).trans hlarge
  
  have hN  := lt_of_lt_of_le hM₀ hMlarge
  
  have hbase  :=
    mem_interior_betheGapRegion (discreteBaseCoordinates_strict_gaps hN hs hcount hcpi hDlarge)
  refine ⟨hbase, ?_, ?_⟩
  · intro ε hε q hq hzero
    by_cases hεzero : ε = 0
    · subst ε
      
      refine ⟨ (discreteCoordinateResidualInv_base_unique hN hs).unique hzero
                   (discreteCoordinateResidualInv_base_zero hN hs)  ▸ hbase, ?_⟩
      exact exists_discreteCoordinateResidualInv_stateEquiv_zero hN hs q
    · let Δ := 1 / ε
      have hΔ  := inverse_parameter_le_cutoff hΔ₀ hε hεzero
      have hvalid  := lt_of_le_of_lt hΔ hΔ₀
      have hInv  := one_div_one_div ε
      have hp  :=
        betheGapRegion_mem_S_n (div_pos hc (by exact_mod_cast hN)) hq
      
      have hBE := (discreteCoordinateResidual_zero_iff hN q).1 (by
                                                                  rw [← discreteCoordinateResidualInv_eq hvalid, hInv]
                                                                  exact hzero)
      have hmesh := fun j => (hq j).2
      
      
      obtain ⟨e, he⟩ := exists_discreteCoordinateResidual_stateEquiv hvalid N (k + 1) q (hmatrix Δ hΔ N k ((le_max_right _ _).trans hlarge) hs _ hp hBE hmesh)
      refine ⟨mem_interior_betheGapRegion  (hbootstrap Δ hΔ N k hMlarge hcount _ hp hs hBE hmesh).2 , e, ?_⟩
      rw [← hInv, discreteCoordinateResidualInv_stateDerivative hvalid,
        ← discreteCoordinateResidual_stateDerivative hvalid]
      exact he
  · intro Δ hΔ q hq hBE hp
    exact (hbootstrap Δ hΔ N k hMlarge hcount _ hp hs hBE  fun j => (hq j).2 ).1

end PottsDiscontinuity.Bethe
