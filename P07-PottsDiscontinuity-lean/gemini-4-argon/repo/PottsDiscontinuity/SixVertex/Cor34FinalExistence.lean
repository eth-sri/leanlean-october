module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theorem23
public import PottsDiscontinuity.SixVertex.Cor34Final

@[expose] public section

open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

noncomputable def cor34BetheLambda (N n : ℕ) (c : ℝ) (p : Fin n → ℝ) : ℝ := by
  classical
  exact if he : Even n then
    2 * ∏ j : Fin n, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖
  else
    let q : ℕ := n / 2 + 1
    let l : Fin n := ⟨q - 1, by
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he; omega⟩
    (2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
      ∑ j ∈ Finset.univ.erase l,
        deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0) *
      ∏ j ∈ Finset.univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖

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
  refine ⟨K, hK, N₀, hN₀, fun N hlarge hEvenN => ?_⟩
  let n : ℕ := N / 2 - r
  obtain ⟨hn, hs, p, hp, hBE, hpAnalytic, ⟨P, hPanalytic, hP0, hformula⟩, hDensity⟩ :=
    hfamily N hlarge hEvenN
  let p₀ : Fin n → ℝ := p d₀
  have hp₀ : p₀ ∈ Bethe.S_n n := hp d₀ le_rfl
  obtain ⟨m, hm⟩ := hEvenN
  have hNform : N = 2 * (n + r) := by dsimp [n]; omega
  have hNpos : 0 < N := by omega
  have hc : 2 < Real.sqrt (2 - 2 * d₀) := by rw [Real.lt_sqrt (by norm_num)]; linarith
  refine ⟨hn, hs, p₀, hp₀, hBE d₀ le_rfl, hDensity d₀ le_rfl, ?_⟩
  change cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p₀ =
    pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n)
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · have hCor := cor34_final_even_all_parameters hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula
      hPanalytic hP0 hNpos hs hn hnEven hNform (Nat.zero_le r) d₀ le_rfl
    rw [Bethe.ratio_eigenvalueRegular hc hp₀] at hCor
    simp only [cor34BetheLambda, hnEven, ↓reduceDIte, ← Complex.ofReal_inj.mp hCor]
    rfl
  · let q : ℕ := n / 2 + 1
    have hnotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hnOdd
    have hnq : n + 1 = 2 * q := by obtain ⟨k, hk⟩ := hnOdd; dsimp [q]; omega
    let l : Fin n := ⟨q - 1, by omega⟩
    have hCor := cor34_final_odd_all_parameters hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula
      hPanalytic hP0 hNpos hs hn hnq hNform (Nat.zero_le r) d₀ le_rfl
    rw [Bethe.ratio_eigenvalueZero hc hp₀ l (cor34_odd_S_n_center_zero hp₀ hnq)] at hCor
    dsimp [cor34BetheLambda]
    rw [dite_eq_right hnotEven]
    exact (Complex.ofReal_inj.mp hCor).symm

end PottsDiscontinuity.SixVertex
