module

public import PottsDiscontinuity.Bethe.Theorem23Bootstrap
public import PottsDiscontinuity.Bethe.Theorem23Density

/-! # Strict quantitative gap improvement at Bethe solutions -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- A fixed outer mesh region has no Bethe solution on its gap boundaries
for large sizes. The additional inequalities on `c,D` make the limiting
explicit configuration lie strictly between the same boundaries. -/
theorem exists_uniform_strict_gap_bootstrap (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ c D K : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      8 * Real.pi * (2 * r + 1 : ℝ) < D ∧ 0 < K ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀), ∀ (N k : ℕ),
      N₀ ≤ N → N = 2 * ((k + 1) + r) →
      ∀ (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N),
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ
        (rootStepError Δ N p (by omega)) ≤ K / N ∧
      ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ∈ Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  obtain ⟨mρ, hmρ, hρ⟩ := rho_uniform_lower_bound hΔ₀
  obtain ⟨mXi, hmXi, hXi⟩ := exists_uniform_Xi_lower_bound hΔ₀
  obtain ⟨M, hM⟩ := rho_uniform_upper_bound hΔ₀
  have hMpos : 0 < M := (rho_pos hΔ₀ 0).trans_le (hM Δ₀ le_rfl 0)
  let B := M + 1 / mXi
  have hB : 0 < B := by positivity
  let c := min Real.pi (1 / (2 * B))
  have hc : 0 < c := lt_min Real.pi_pos (by positivity)
  let D := 4 * (2 * r + 1 : ℝ) / mρ + 8 * Real.pi * (2 * r + 1 : ℝ)
  have hDlarge : 8 * Real.pi * (2 * r + 1 : ℝ) < D := by
    dsimp [D]
    have hpos : 0 < 4 * (2 * r + 1 : ℝ) / mρ := by positivity
    linarith
  have hD : 0 < D := lt_trans (by positivity) hDlarge
  obtain ⟨K, hK, M₀, _, hestimate⟩ := exists_uniform_density_bound_of_Bethe_mesh r hΔ₀ D hD
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max K (2 * K / (mρ * mXi)))
  have hN₀pos := hK.trans ((le_max_left _ _).trans_lt hN₀)
  have hN₀nat : 0 < N₀ := by exact_mod_cast hN₀pos
  refine ⟨c, D, K, hc, min_le_left _ _, hDlarge, hK, max M₀ N₀, hN₀nat.trans_le (le_max_right ..),
    fun Δ hΔ N k hlarge hcount p hp hs hBE hmesh => ?_⟩
  have hn := (le_max_right M₀ N₀).trans hlarge
  have hb := rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) (N := N) p (by omega)
  have herr := hestimate Δ hΔ N k ((le_max_left ..).trans hlarge) hcount p hp hs hBE hmesh
  have hNc : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hN₀nat hn)
  have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hn
  have hKN := ((le_max_left _ _).trans_lt hN₀).trans_le hcast
  have hsmall : K / ((N : ℝ) * mXi) ≤ mρ / 2 := by
    apply (div_le_iff₀ (mul_pos hNc hmXi)).2
    have ht :=
      ((le_max_right _ _).trans_lt hN₀).trans_le hcast
    have ht' := (div_lt_iff₀ (mul_pos hmρ hmXi)).mp ht
    nlinarith only [ht']
  refine ⟨herr, fun j => ?_⟩
  have hk : 0 < k + 1 := by omega
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hk j
  let t := rootPartitionPoint (k + 1) p hk j.succ - rootPartitionPoint (k + 1) p hk j.castSucc
  let a := rootGapMultiplicity N (k + 1) j
  have ht : 0 < (N : ℝ) * t := mul_pos hNc (rootPartition_gap_pos hp hk j)
  have hpoint (E : ℝ) (he : densityNorm Δ (rootStepError Δ N p hk) ≤ E) :
      |a / ((N : ℝ) * t) - rho Δ x| ≤ E / mXi := by
    have h := densityNorm_x_pointwise_le hΔ₀ hΔ _ hb E mXi hmXi (hXi Δ hΔ) he hx
    simpa only [rootStepError, rootStepDensity_on_cell hp hk hs j hcell] using h
  have hlo := (div_le_iff₀ ht).mp (show a / ((N : ℝ) * t) ≤ B by
    dsimp only [B]
    linarith [(abs_le.mp (hpoint 1 (herr.trans ((div_le_one hNc).2 hKN.le)))).2, hM Δ hΔ x])
  have hhi := (le_div_iff₀ ht).mp (show mρ / 2 ≤ a / ((N : ℝ) * t) by
    have h := (abs_le.mp (hpoint _ herr)).1
    rw [div_div] at h
    linarith only [(neg_le_neg hsmall).trans h, hρ Δ hΔ x hx])
  refine ⟨?_, ?_⟩
  · have hmid : 1 / ((N : ℝ) * B) ≤ t :=
      (div_le_iff₀ (mul_pos hNc hB)).2 (by nlinarith only [hlo, one_le_rootGapMultiplicity hs j])
    have hclt : c < 1 / B := by
      have hcB : c ≤ 1 / (2 * B) := min_le_right _ _
      have hhalf : 1 / (2 * B) < 1 / B := by
        apply one_div_lt_one_div_of_lt hB
        linarith
      exact hcB.trans_lt hhalf
    calc
      c / (N : ℝ) < (1 / B) / (N : ℝ) := div_lt_div_of_pos_right hclt hNc
      _ = 1 / ((N : ℝ) * B) := by rw [div_div, mul_comm B (N : ℝ)]
      _ ≤ _ := hmid
  · have hu : t ≤ 2 * a / (mρ * (N : ℝ)) :=
      (le_div_iff₀ (mul_pos hmρ hNc)).2 (by nlinarith only [hhi])
    have hmass := rootGapMultiplicity_le_offset hs hcount j
    have hDlt : 2 * (2 * r + 1 : ℝ) / mρ < D := by
      dsimp [D]
      have hpi : 0 < 8 * Real.pi * (2 * r + 1 : ℝ) := by positivity
      rw [show 4 * (2 * r + 1 : ℝ) / mρ = 2 * (2 * (2 * r + 1 : ℝ) / mρ) by ring]
      have hpos2 : 0 < 2 * (2 * r + 1 : ℝ) / mρ := by positivity
      linarith
    calc
      _ ≤ 2 * rootGapMultiplicity N (k + 1) j / (mρ * (N : ℝ)) := hu
      _ ≤ 2 * (2 * r + 1 : ℝ) / (mρ * (N : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity)
      _ = (2 * (2 * r + 1 : ℝ) / mρ) / (N : ℝ) := by rw [div_div]
      _ < D / (N : ℝ) := div_lt_div_of_pos_right hDlt hNc

end PottsDiscontinuity.Bethe
