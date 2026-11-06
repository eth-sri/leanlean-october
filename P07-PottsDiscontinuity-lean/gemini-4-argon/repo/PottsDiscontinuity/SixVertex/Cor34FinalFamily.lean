module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34FinalNormalization
public import PottsDiscontinuity.SixVertex.Cor34FinalWave

@[expose] public section

open Filter Topology
open Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_eventually_S_n_and_BE {N n : ℕ}
    {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPcont : ContinuousAt P 0) (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      cor34_normalizedBlockWave (N := N) ε (P ε) ≠ 0 ∧
      ε < 0 ∧ 1 / ε < -1 ∧ P ε ∈ Bethe.S_n n ∧
      Bethe.DiscreteBetheEquation (1 / ε) N n (P ε) := by
  have hInv : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa only [one_div] using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  filter_upwards [cor34_final_eventually_normalizedBlockWave_ne_zero hPcont hP0 hNpos hbound,
    hInv, self_mem_nhdsWithin] with ε hw hΔ hε
  have hε' : ε < 0 := hε
  have hrecip : 1 / (1 / ε) = ε := one_div_one_div ε
  have hPEq : P ε = p (1 / ε) := by rw [hformula (1 / ε) hΔ, hrecip]
  exact ⟨hw, hε', lt_of_le_of_lt hΔ hd₀, hPEq ▸ hp (1 / ε) hΔ, hPEq ▸ hBE (1 / ε) hΔ⟩

theorem cor34_final_even_family_eventually_physical_pfRoot {N n r : ℕ}
    {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) (P ε) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) :=
  cor34_even_bethe_branch_eventually_physical_pfRoot
    hPanalytic.continuousAt hP0 hNpos hbound hnpos hn hN hr
    ((cor34_final_eventually_S_n_and_BE hd₀ hp hBE hformula
      hPanalytic.continuousAt hP0 hNpos hbound).mono fun _ ⟨hw, hε, hInv, hS, hBEε⟩ =>
      ⟨hw, cor34_final_even_normalized_eigen hε hInv _ hS hn hBEε⟩)

theorem cor34_final_odd_family_eventually_physical_pfRoot {N n q r : ℕ}
    {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) (P ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) :=
  cor34_odd_bethe_branch_eventually_physical_pfRoot
    hPanalytic.continuousAt hP0 hNpos hbound hnpos hnq hN hr
    ((cor34_final_eventually_S_n_and_BE hd₀ hp hBE hformula
      hPanalytic.continuousAt hP0 hNpos hbound).mono fun _ ⟨hw, hε, hInv, hS, hBEε⟩ =>
      ⟨hw, cor34_final_odd_normalized_eigen hε hInv _ hS hnq hBEε⟩)

end PottsDiscontinuity.SixVertex
