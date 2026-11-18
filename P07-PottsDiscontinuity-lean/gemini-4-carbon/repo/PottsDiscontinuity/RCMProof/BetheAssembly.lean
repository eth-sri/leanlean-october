module

public import Mathlib
public import PottsDiscontinuity.Bethe.RatioBulk29
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

/-! # Theorem 1.3 ratio limit at the critical six-vertex parameter -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

/-- Theorem 1.3, equation (1.7), along the tail of the subsequence `N ∈ 4ℕ`. -/
theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : ℕ, ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (Real.arcosh (Real.sqrt q / 2))) atTop (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) * (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  let Δcrit : ℝ := -Real.sqrt q / 2
  let c : ℝ := Real.sqrt (2 + Real.sqrt q)
  have hsqrtq : 2 < Real.sqrt q := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ q), Real.sqrt_nonneg q]
  have hΔcrit : Δcrit < -1 := by dsimp [Δcrit]; linarith
  have hlamEq : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) :=
    (Bethe.eq_lamOf (Real.arcosh_pos (by linarith))
      (by dsimp [Δcrit]; rw [neg_div, neg_neg]; exact Real.cosh_arcosh (by linarith))).symm
  have hcΔ : BetheAnsatz.anisotropy c = Δcrit := by
    dsimp [BetheAnsatz.anisotropy, c, Δcrit]; rw [Real.sq_sqrt (by positivity)]; ring
  have hcPhys : Real.sqrt (2 - 2 * Δcrit) = c := by dsimp [Δcrit, c]; congr 1; ring
  have hc2 : 2 < c := by dsimp [c]; rw [Real.lt_sqrt (by norm_num)]; linarith
  obtain ⟨Kq, _, Nq, _, hEndQ⟩ := SixVertex.cor34_final_exists_family_at_endpoint r hΔcrit
  obtain ⟨Kp, _, Np, _, hEndP⟩ := SixVertex.cor34_final_exists_family_at_endpoint 0 hΔcrit
  let B : ℕ := max (max Nq Np) (r + 2)
  let N (i : ℕ) := 4 * (i + B)
  have hhalf (i : ℕ) : N i / 2 = 2 * (i + B) := by dsimp [N]; omega
  have hNpos (i : ℕ) : 0 < N i := by dsimp [N]; omega
  have hNeven (i : ℕ) : Even (N i) := ⟨2 * (i + B), by dsimp [N]; omega⟩
  have hrBound (i : ℕ) : r ≤ N i / 2 := by rw [hhalf]; dsimp [B]; omega
  have hnQ (i : ℕ) : 0 < N i / 2 - r := by rw [hhalf]; dsimp [B]; omega
  have hsizeQ (i : ℕ) : 2 * (N i / 2 - r) ≤ N i := by rw [hhalf]; dsimp [N]; omega
  have hnP (i : ℕ) : 0 < N i / 2 := by rw [hhalf]; dsimp [B]; omega
  have hsizeP (i : ℕ) : 2 * (N i / 2) ≤ N i := by rw [hhalf]; dsimp [N]; omega
  choose _ _ rootsQ hrootsQmem hrootsQBE hnormQ hLambdaQ using
    fun i => hEndQ (N i) (by dsimp [N, B]; omega) (hNeven i)
  choose _ _ rootsP hrootsPmem hrootsPBE hnormP hLambdaP using
    fun i => hEndP (N i) (by dsimp [N, B]; omega) (hNeven i)
  have hNlim : Tendsto (fun i : ℕ => (N i : ℝ)) atTop atTop :=
    Filter.tendsto_atTop.2 fun x => by
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil x)] with i hi
      exact (Nat.le_ceil x).trans (by exact_mod_cast (show Nat.ceil x ≤ N i by dsimp [N]; omega))
  let hbp (i : ℕ) := Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsP i) (hrootsPmem i) (hnP i) (hsizeP i)
  let hbq (i : ℕ) := Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsQ i) (hrootsQmem i) (hnQ i) (hsizeQ i)
  let K : ℝ := max Kp Kq
  have hK : 0 ≤ K := by
    have hnn := Bethe.densityNorm_nonneg hΔcrit
      (f := fun x => Bethe.rootStepDensity (N 0) (N 0 / 2) (rootsP 0) (hrootsPmem 0) (hnP 0) (hsizeP 0) x - Bethe.rho Δcrit x) (hbp 0)
    exact le_trans (by nlinarith [hnormP 0, show (0 : ℝ) < N 0 by exact_mod_cast hNpos 0]) (le_max_left _ _)
  have hrate : ∀ᶠ i : ℕ in atTop,
      Bethe.densityNorm Δcrit hΔcrit _ (hbp i) ≤ K / N i ∧
      Bethe.densityNorm Δcrit hΔcrit _ (hbq i) ≤ K / N i :=
    Filter.Eventually.of_forall fun i =>
      ⟨(hnormP i).trans (div_le_div_of_nonneg_right (le_max_left Kp Kq) (by positivity)),
       (hnormQ i).trans (div_le_div_of_nonneg_right (le_max_right Kp Kq) (by positivity))⟩
  have hSdata : ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial (Bethe.lamOf Δcrit)) atTop (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
         else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i) ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) /
          BetheAnsatz.eigenvalueRegular c (rootsP i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) := by
    by_cases hrEven : r % 2 = 0
    · obtain ⟨S, hS, hr'⟩ := Bethe.ratio_even_eigenvalue_limit_fourier
        hΔcrit r N (fun i => ⟨i + B, rfl⟩) hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate hrEven hr hc2 hcΔ
      exact ⟨S, hS, by simpa [hrEven] using hr'⟩
    · obtain ⟨S, hS, hr'⟩ := Bethe.ratio_odd_eigenvalue_limit_fourier
        hΔcrit r N (fun i => ⟨i + B, rfl⟩) hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate hrEven hr hc2 hcΔ
      exact ⟨S, hS, by simpa [hrEven] using hr'⟩
  obtain ⟨S, hS, hratio⟩ := hSdata
  have hPFtop (i : ℕ) : BetheAnsatz.eigenvalueRegular c (rootsP i) = (Lambda c (N i) 0 : ℂ) := by
    have hp : Even (N i / 2) := ⟨i + B, by rw [hhalf]; omega⟩
    rw [← show SixVertex.cor34BetheLambda (N i) (N i / 2) c (rootsP i) = Lambda c (N i) 0 by simpa [hcPhys] using hLambdaP i]
    simpa [SixVertex.cor34BetheLambda, hp] using Bethe.ratio_eigenvalueRegular hc2 (hrootsPmem i)
  have hPFnum (i : ℕ) :
      (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
       else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i) ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) =
        (Lambda c (N i) r : ℂ) := by
    rw [← show SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) = Lambda c (N i) r by simpa [hcPhys] using hLambdaQ i]
    by_cases hrEven : r % 2 = 0
    · have hp : Even (N i / 2 - r) := ⟨(N i / 2 - r) / 2, by rw [hhalf]; omega⟩
      simpa [hrEven, SixVertex.cor34BetheLambda, hp] using Bethe.ratio_eigenvalueRegular hc2 (hrootsQmem i)
    · have hp : ¬ Even (N i / 2 - r) := fun ⟨k, hk⟩ => hrEven (by rw [hhalf] at hk; omega)
      let l : Fin (N i / 2 - r) := ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩
      have hcenter : rootsQ i l = 0 := by
        simpa [l] using cor34_odd_S_n_center_zero (hrootsQmem i)
          (show N i / 2 - r + 1 = 2 * ((N i / 2 - r) / 2 + 1) by rw [hhalf]; omega)
      simpa [hrEven, SixVertex.cor34BetheLambda, hp, l] using Bethe.ratio_eigenvalueZero (N := N i) hc2 (hrootsQmem i) l hcenter
  have hquot : Tendsto (fun i : ℕ => ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) :=
    hratio.congr fun i => by rw [hPFnum i, hPFtop i]; push_cast; rfl
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hquot
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  exact ⟨B, S, by simpa [hlamEq] using hS, by simpa [N, c, hlamEq] using hre⟩

end PottsDiscontinuity.RCMProof
