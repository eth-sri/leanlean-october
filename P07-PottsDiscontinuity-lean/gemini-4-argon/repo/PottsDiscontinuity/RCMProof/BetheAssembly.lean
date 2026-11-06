module

public import Mathlib
public import PottsDiscontinuity.Bethe.RatioAnySign
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : ℕ, ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q / 2))) atTop
        (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) *
          (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  let Δcrit : ℝ := -Real.sqrt q / 2
  let c : ℝ := Real.sqrt (2 + Real.sqrt q)
  have hsqrtq : 2 < Real.sqrt q := by
    nlinarith [Real.sq_sqrt (show 0 ≤ q by linarith), Real.sqrt_nonneg q]
  have hΔcrit : Δcrit < -1 := by dsimp [Δcrit]; linarith
  have hlam : 0 < Real.arcosh (Real.sqrt q / 2) := Real.arcosh_pos (by linarith)
  have hlamEq : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) := by
    refine (Bethe.eq_lamOf hlam ?_).symm
    rw [Real.cosh_arcosh (by linarith)]
    dsimp [Δcrit]; ring
  have hcΔ : BetheAnsatz.anisotropy c = Δcrit := by
    have hc2 : c ^ 2 = 2 + Real.sqrt q := Real.sq_sqrt (by positivity)
    dsimp [BetheAnsatz.anisotropy, Δcrit]; linarith
  have hcPhysical : Real.sqrt (2 - 2 * Δcrit) = c := by
    dsimp [Δcrit, c]; congr 1; ring
  have hc2 : 2 < c := by
    dsimp [c]; rw [Real.lt_sqrt (by norm_num)]; linarith

  obtain ⟨Kq, hKq, Nq, hNq, hEndpointQ⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint r hΔcrit
  obtain ⟨Kp, hKp, Np, hNp, hEndpointP⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint 0 hΔcrit
  let B : ℕ := max (max Nq Np) (r + 2)
  let N : ℕ → ℕ := fun i => 4 * (i + B)
  have hBq : Nq ≤ B := (le_max_left Nq Np).trans (le_max_left _ _)
  have hBp : Np ≤ B := (le_max_right Nq Np).trans (le_max_left _ _)
  have hBr : r + 2 ≤ B := le_max_right _ _
  have hhalf (i : ℕ) : N i / 2 = 2 * (i + B) := by dsimp [N]; omega
  have hNpos (i : ℕ) : 0 < N i := by dsimp [N]; omega
  have hNeven (i : ℕ) : Even (N i) := ⟨2 * (i + B), by dsimp [N]; omega⟩
  have hNlargeQ (i : ℕ) : Nq ≤ N i := hBq.trans (by dsimp [N]; omega)
  have hNlargeP (i : ℕ) : Np ≤ N i := hBp.trans (by dsimp [N]; omega)
  have h4 (i : ℕ) : 4 ∣ N i := ⟨i + B, rfl⟩
  have hNlim : Tendsto (fun i : ℕ => (N i : ℝ)) atTop atTop :=
    Filter.tendsto_atTop.2 fun x => by
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil x)] with i hi
      exact (Nat.le_ceil x).trans (by exact_mod_cast (show Nat.ceil x ≤ N i by dsimp [N]; omega))
  have hrBound (i : ℕ) : r ≤ N i / 2 := by rw [hhalf]; omega
  have hnQ (i : ℕ) : 0 < N i / 2 - r := by rw [hhalf]; omega

  choose hnQ' hsizeQ rootsQ hrootsQmem hrootsQBE hnormQ hLambdaQ using
    fun i => hEndpointQ (N i) (hNlargeQ i) (hNeven i)
  choose hnP' hsizeP rootsP hrootsPmem hrootsPBE hnormP hLambdaP using
    fun i => hEndpointP (N i) (hNlargeP i) (hNeven i)
  have hbp (i : ℕ) := Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsP i)
    (hrootsPmem i) (hnP' i) (hsizeP i)
  have hbq (i : ℕ) := Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsQ i)
    (hrootsQmem i) (hnQ' i) (hsizeQ i)
  let K : ℝ := max Kp Kq
  have hK : 0 ≤ K := by positivity
  have hrate : ∀ᶠ i : ℕ in atTop,
      Bethe.densityNorm Δcrit hΔcrit
        (fun x => Bethe.rootStepDensity (N i) (N i / 2) (rootsP i) (hrootsPmem i)
          (hnP' i) (hsizeP i) x - Bethe.rho Δcrit x) (hbp i) ≤ K / N i ∧
      Bethe.densityNorm Δcrit hΔcrit
        (fun x => Bethe.rootStepDensity (N i) (N i / 2 - r) (rootsQ i) (hrootsQmem i)
          (hnQ' i) (hsizeQ i) x - Bethe.rho Δcrit x) (hbq i) ≤ K / N i :=
    Filter.Eventually.of_forall fun i =>
      ⟨(hnormP i).trans (div_le_div_of_nonneg_right (le_max_left Kp Kq) (by positivity)),
        (hnormQ i).trans (div_le_div_of_nonneg_right (le_max_right Kp Kq) (by positivity))⟩

  have hSdata : ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (Bethe.lamOf Δcrit)) atTop (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
         else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
           ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) /
          BetheAnsatz.eigenvalueRegular c (rootsP i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) := by
    by_cases hrEven : r % 2 = 0
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_even_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate hrEven hr hcΔ
      exact ⟨S, hS, by simpa [hrEven] using hratio⟩
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_odd_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate hrEven hr hcΔ
      exact ⟨S, hS, by simpa [hrEven] using hratio⟩
  obtain ⟨S, hS, hratio⟩ := hSdata

  have hPFtop (i : ℕ) : BetheAnsatz.eigenvalueRegular c (rootsP i) =
      ((Lambda c (N i) 0 : ℝ) : ℂ) := by
    have hparity : Even (N i / 2) := ⟨i + B, by rw [hhalf]; omega⟩
    have hreal : BetheAnsatz.eigenvalueRegular c (rootsP i) =
        ((SixVertex.cor34BetheLambda (N i) (N i / 2) c (rootsP i) : ℝ) : ℂ) := by
      simpa [SixVertex.cor34BetheLambda, hparity] using Bethe.ratio_eigenvalueRegular hc2 (hrootsPmem i)
    rw [hreal, ← hcPhysical]
    exact congrArg (fun x : ℝ => (x : ℂ)) (hLambdaP i)
  have hPFnum (i : ℕ) :
      (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
       else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
         ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) =
        ((Lambda c (N i) r : ℝ) : ℂ) := by
    by_cases hrEven : r % 2 = 0
    · simp only [hrEven, ↓reduceIte]
      have hparity : Even (N i / 2 - r) := ⟨(N i / 2 - r) / 2, by rw [hhalf]; omega⟩
      have hreal : BetheAnsatz.eigenvalueRegular c (rootsQ i) =
          ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := by
        simpa [SixVertex.cor34BetheLambda, hparity] using Bethe.ratio_eigenvalueRegular hc2 (hrootsQmem i)
      rw [hreal, ← hcPhysical, hLambdaQ i]
    · simp only [hrEven, ↓reduceIte]
      have hparity : ¬ Even (N i / 2 - r) := by
        rintro ⟨k, hk⟩; apply hrEven; rw [hhalf] at hk; omega
      let qcenter : ℕ := (N i / 2 - r) / 2 + 1
      have hnq : N i / 2 - r + 1 = 2 * qcenter := by
        obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hparity; dsimp [qcenter]; omega
      let l : Fin (N i / 2 - r) := ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩
      have hcenter : rootsQ i l = 0 := by
        simpa [l, qcenter] using cor34_odd_S_n_center_zero (hrootsQmem i) hnq
      have hreal : BetheAnsatz.eigenvalueZero (N i) c (rootsQ i) l =
          ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := by
        simpa [SixVertex.cor34BetheLambda, hparity, qcenter, l] using
          Bethe.ratio_eigenvalueZero (N := N i) hc2 (hrootsQmem i) l hcenter
      rw [hreal, ← hcPhysical, hLambdaQ i]
  have hcomplex : Tendsto (fun i : ℕ => ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) :=
    hratio.congr fun i => by rw [hPFnum i, hPFtop i]; push_cast; rfl
  have hreal : Tendsto (fun i : ℕ => Lambda c (N i) r / Lambda c (N i) 0) atTop
      (𝓝 (Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S)))) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  exact ⟨B, S, hlamEq ▸ hS, by simpa [N, c, hlamEq] using hreal⟩

end PottsDiscontinuity.RCMProof
