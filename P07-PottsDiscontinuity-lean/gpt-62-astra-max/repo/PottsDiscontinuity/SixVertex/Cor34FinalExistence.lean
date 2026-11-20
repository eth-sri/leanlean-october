module

public import PottsDiscontinuity.Bethe.RatioProducts
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
      have ho : Odd n := Nat.not_even_iff_odd.mp he
      obtain ⟨k, hk⟩ := ho
      omega
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
        Bethe.densityNorm d₀
          (fun x => Bethe.rootStepDensity N p hn x - Bethe.rho d₀ x) ≤ K / N ∧
        cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p =
          Lambda (Real.sqrt (2 - 2 * d₀)) N r := by
  obtain ⟨K, hK, N₀, hN₀, d₁, hd₀₁, hd₁, hfamily⟩ := Bethe.theorem23 r hd₀
  refine ⟨K, hK, N₀, hN₀, ?_⟩
  intro N hlarge hEvenN
  let n : ℕ := N / 2 - r
  obtain ⟨hn, hs, p, hp, hBE, hpAnalytic, hP, hDensity⟩ := hfamily N hlarge hEvenN
  obtain ⟨P, hPanalytic, hP0, hformula⟩ := hP
  let c := rowParameter d₀
  let p₀ := p d₀
  have hS := hp d₀ le_rfl
  have hselect := physical_endpoint hd₀ hn hs hPanalytic.continuousAt hP0 hformula
  have ha {d : ℝ} (h : d ≤ d₀) := hpAnalytic d (h.trans_lt hd₀₁)
  have hlt {d : ℝ} (h : d ≤ d₀) := h.trans_lt hd₀
  refine ⟨hn,hs,p₀,hS,hBE _ le_rfl,hDensity _ le_rfl,?_⟩
  change cor34BetheLambda N n c p₀ = pfRoot (transferBlock N c n)
  by_cases he : Even n
  · have h := hselect (fun d => BetheAnsatz.eigenvalueRegular (rowParameter d) (p d))
      (fun d h => analytic_eigenvalueRegular (hlt h) (ha h) (hp _ h) (cor34_even_S_n_roots_nonzero (hp _ h) he))
      (fun d h => cor34_final_even_block_eigen (rowParameter_gt (hlt h)) (rowParameter_anisotropy (hlt h)) _ (hp _ h) he (hBE _ h))
    have hr := congrArg Complex.re (h.trans (Bethe.ratio_eigenvalueRegular (rowParameter_gt hd₀) hS))
    simpa only [cor34BetheLambda,dite_eq_left he,Complex.ofReal_re] using hr.symm
  · let q := n/2+1
    have hq : n+1 = 2*q := by obtain ⟨k,hk⟩ := Nat.not_even_iff_odd.mp he; dsimp [q]; omega
    let l : Fin n := ⟨q-1,by omega⟩
    have hcenter {d : ℝ} (h : d ≤ d₀) : p d l = 0 := cor34_odd_S_n_center_zero (hp d h) hq
    have h := hselect (fun d => BetheAnsatz.eigenvalueZero N (rowParameter d) (p d) l)
      (fun d h => analytic_eigenvalueZero (hlt h) (ha h) N l (hp _ h) fun j hj hz => hj (cor34_S_n_injective (hp _ h) (hz.trans (hcenter h).symm)))
      (fun d h => cor34_final_odd_block_eigen (rowParameter_gt (hlt h)) (rowParameter_anisotropy (hlt h)) _ (hp _ h) hq (hBE _ h))
    have hr := congrArg Complex.re (h.trans (Bethe.ratio_eigenvalueZero (rowParameter_gt hd₀) hS l (hcenter le_rfl)))
    simpa only [cor34BetheLambda,dite_eq_right he,Complex.ofReal_re] using hr.symm

end PottsDiscontinuity.SixVertex
