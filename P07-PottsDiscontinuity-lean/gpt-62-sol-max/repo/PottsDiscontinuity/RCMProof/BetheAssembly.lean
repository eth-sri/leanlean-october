module

public import PottsDiscontinuity.Bethe.RatioLimit
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

/-!
# Theorem 1.3 ratio limit at the critical six-vertex parameter

The assembly uses Theorem 2.3 to select the two symmetric Bethe families,
the Fourier eigenvalue-ratio limit for both parities (`Bethe/Ratio*`), and the
proved Corollary 3.4 analytic-family identifications.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

/-- Theorem 1.3, equation (1.7), along the tail of the subsequence `N ∈ 4ℕ`.
The finite-size Bethe/Perron-root identification uses the proved Corollary 3.4
endpoint-family theorem. -/
private theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q / 2))) atTop
        (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * i) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * i) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) *
          (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  let Δcrit : ℝ := -Real.sqrt q / 2
  let c : ℝ := Real.sqrt (2 + Real.sqrt q)
  have hsqrtq : 2 < Real.sqrt q := (Real.lt_sqrt (by norm_num)).mpr (by grind)
  have hc : 2 < c := (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  have hΔcrit : Δcrit < -1 := by grind
  have hlam : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) := by
    unfold Bethe.lamOf Δcrit
    congr 1
    ring
  have hcΔ : anisotropy c = Δcrit := by
    unfold anisotropy c Δcrit
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hcPhysical : Real.sqrt (2 - 2 * Δcrit) = c := by grind

  obtain ⟨Kq, hKq, Nq, _, hQ⟩ := cor34_final_exists_family_at_endpoint r hΔcrit
  obtain ⟨Kp, hKp, Np, _, hP⟩ := cor34_final_exists_family_at_endpoint 0 hΔcrit
  let B : ℕ := max (max Nq Np) (r + 2)
  let N (i : ℕ) := 4 * (i + B)
  have h4 (i : ℕ) : 4 ∣ N i := ⟨i + B, rfl⟩
  have hN (i : ℕ) : 0 < N i := by dsimp [N, B]; omega
  have hEven (i : ℕ) : Even (N i) := by rw [Nat.even_iff]; dsimp [N]; omega
  have hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun i => by exact_mod_cast (show i ≤ N i by dsimp [N]; omega))
      tendsto_natCast_atTop_atTop
  have hrN (i : ℕ) : r ≤ N i / 2 := by dsimp [N, B]; omega
  choose hnq hsq Q hqmem hqBE hqNorm hqΛ using
    fun i => hQ (N i) (by dsimp [N, B]; omega) (hEven i)
  choose hnp hsp P hpmem hpBE hpNorm hpΛ using
    fun i => hP (N i) (by dsimp [N, B]; omega) (hEven i)
  rw [hcPhysical] at hpΛ hqΛ
  have hrate := Eventually.of_forall (f := atTop) fun i =>
    And.intro ((hpNorm i).trans (div_le_div_of_nonneg_right (le_max_left Kp Kq) (by positivity)))
      ((hqNorm i).trans (div_le_div_of_nonneg_right (le_max_right Kp Kq) (by positivity)))
  obtain ⟨S, hS, hratio⟩ := ratio_eigenvalue_limit_fourier hΔcrit r N h4 hrN hN hnq P Q
    hpmem hqmem hpBE hqBE hNlim hrate hc hcΔ
  have hPval (i : ℕ) : eigenvalueRegular c (P i) = (Lambda c (N i) 0 : ℂ) := by
    simpa only [parityEigenvalue, dite_eq_left ((even_sector_iff (h4 i) (Nat.zero_le _)).mpr rfl)]
      using hpΛ i
  have hcast := hratio.congr (f₂ := fun i => ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ))
    (fun i => by simp [hqΛ i, hPval i])
  refine ⟨S, ?_, (tendsto_add_atTop_iff_nat B).1 ?_⟩
  · simpa [hlam] using hS
  · simpa only [Function.comp_def, Complex.ofReal_re, hlam] using
          (Complex.continuous_re.continuousAt.tendsto.comp hcast)

/-- The spectral gap of a fixed sector along widths divisible by four. -/
noncomputable def sectorLogGap (c : ℝ) (N r : ℕ) : ℝ :=
  Real.log (Lambda c N r) - Real.log (Lambda c N 0)

theorem sectorLogGap_tendsto (q : ℝ) (hq : 4 < q) (r : ℕ) {S : ℝ}
    (hS : Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q / 2))) atTop (𝓝 S)) :
    Tendsto (fun n : ℕ => sectorLogGap (Real.sqrt (2 + Real.sqrt q)) (4 * n) r) atTop
      (𝓝 (-(r : ℝ) * (Real.arcosh (Real.sqrt q / 2) + 2 * S))) := by
  obtain ⟨T, hT, h⟩ := apply_17_at_critical_c q hq r
  rw [tendsto_nhds_unique hT hS] at h
  have ht := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp h
  rw [Real.log_exp] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop r] with n hn
  exact Real.log_div (Lambda_pos (by positivity) (by omega : r ≤ 4 * n / 2)).ne'
    (Lambda_pos (by positivity) (Nat.zero_le (4 * n / 2))).ne'

end PottsDiscontinuity.RCMProof
