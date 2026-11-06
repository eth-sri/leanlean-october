module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theorem23
public import PottsDiscontinuity.SixVertex.Cor34Final

/-! # Endpoint and existence forms of Corollary 3.4 -/

@[expose] public section

open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The real Bethe eigenvalue `Λ(p)` in the two source formulas, selected by root parity. -/
noncomputable def cor34BetheLambda (N n : ℕ) (c : ℝ) (p : Fin n → ℝ) : ℝ := by
  classical
  exact if he : Even n then
    2 * ∏ j : Fin n, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖
  else
    let q : ℕ := n / 2 + 1
    let l : Fin n := ⟨q - 1, by
      grind
    ⟩
    (2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
      ∑ j ∈ Finset.univ.erase l,
        deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0) *
      ∏ j ∈ Finset.univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖

/-- Theorem 2.3 supplies a density-controlled Bethe state at `Δ₀`; Corollary 3.4 identifies its
real Bethe eigenvalue with the `r`-sector Perron root for every sufficiently large even `N`. -/
theorem cor34_final_exists_family_at_endpoint (r : ℕ) {d₀ : ℝ} (hd₀ : d₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N, ∃ p : Fin n → ℝ,
        ∃ hp : p ∈ Bethe.S_n n,
        Bethe.DiscreteBetheEquation d₀ N n p ∧
        Bethe.densityNorm d₀ hd₀
          (fun x => Bethe.rootStepDensity N n p hp hn hs x - Bethe.rho d₀ x)
          (Bethe.rootStepDensity_error_bddAbove hd₀ _ hp hn hs) ≤ K / N ∧
        cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p =
          Lambda (Real.sqrt (2 - 2 * d₀)) N r := by
  obtain ⟨K, hK, N₀, hN₀, d₁, hd₀₁, hd₁, hfamily⟩ := Bethe.theorem23 r hd₀
  refine ⟨K, hK, N₀, hN₀, ?_⟩
  intro N hlarge hEvenN
  let n := N / 2 - r
  obtain ⟨hn, hs, p, hp, hBE, hpAnalytic, hP, hDensity⟩ := hfamily N hlarge hEvenN
  obtain ⟨P, hPanalytic, hP0, hformula⟩ := hP
  let p₀ := p d₀
  have hp₀ :=
    hp d₀ le_rfl
  obtain ⟨m, hm⟩ := hEvenN
  have hNform : N = 2 * (n + r) := by
    omega
  have hNpos : 0 < N := by omega
  have hc : 2 < Real.sqrt (2 - 2 * d₀) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  refine ⟨hn, hs, p₀, hp₀, hBE d₀ le_rfl, hDensity d₀ le_rfl, ?_⟩
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · have h := cor34_final_generic (fun c p => BetheAnsatz.eigenvalueRegular c p)
      cor34_normalizedRegularEigenvalue (fun _ => False) hd₀₁ hd₁ hpAnalytic hp
      (fun d hd j => .inr (cor34_even_S_n_roots_nonzero (hp d hd) hnEven j)) hBE hformula hPanalytic hP0
      hNpos hs hn (fun ε _ hε p => cor34_normalizedRegularEigenvalue_scale ε hε p)
      (fun c Δ hc hΔ p hp hBE => cor34_final_even_block_eigen hc hΔ p hp hnEven hBE)
      (cor34_normalizedRegularEigenvalue_tendsto_pfRoot hPanalytic.continuousAt hP0 hNpos hs hn
        hnEven hNform)
      (fun d hd h => cor34_final_analyticAt_normalizedRegular hd₁ hpAnalytic hd
        (fun j => (h j).1) (fun j => (h j).2.resolve_left id)) d₀ le_rfl
    rw [Bethe.ratio_eigenvalueRegular hc hp₀] at h
    rw [cor34BetheLambda, dif_pos hnEven]
    exact h.symm
  · let q := n / 2 + 1
    have hnotEven := Nat.not_even_iff_odd.mpr hnOdd
    obtain ⟨k, hk⟩ := hnOdd
    have hnq : n + 1 = 2 * q := by omega
    let l : Fin n := ⟨q - 1, by omega⟩
    have h := cor34_final_generic (fun c p => BetheAnsatz.eigenvalueZero N c p l)
      (fun ε p => cor34_normalizedZeroEigenvalue ε p l) (· = l) hd₀₁ hd₁ hpAnalytic hp
      (fun d hd j => or_iff_not_imp_left.2 fun hj h => hj (cor34_S_n_injective (hp d hd)
        (h.trans (cor34_odd_S_n_center_zero (hp d hd) hnq).symm))) hBE
      hformula hPanalytic hP0 hNpos hs hn (fun ε hεlo hε p => cor34_normalizedZeroEigenvalue_scale l ε hεlo hε p)
      (fun c Δ hc hΔ p hp hBE => cor34_final_odd_block_eigen hc hΔ p hp hnq hBE)
      (cor34_normalizedZeroEigenvalue_tendsto_pfRoot hPanalytic.continuousAt hP0 hNpos hs hn hnq hNform)
      (fun d hd h => cor34_final_analyticAt_normalizedZero hd₁ hpAnalytic hd l
        (fun j => (h j).1) (fun j => (h j).2)) d₀ le_rfl
    rw [Bethe.ratio_eigenvalueZero hc hp₀ l (cor34_odd_S_n_center_zero hp₀ hnq)] at h
    rw [cor34BetheLambda, dif_neg hnotEven]
    exact h.symm

end PottsDiscontinuity.SixVertex
