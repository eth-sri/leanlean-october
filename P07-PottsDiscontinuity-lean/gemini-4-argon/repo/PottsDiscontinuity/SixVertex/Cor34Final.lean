module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34FinalAnalytic
public import PottsDiscontinuity.SixVertex.Cor34FinalFamily

@[expose] public section

open Filter Topology Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_extension_cancel {n : ℕ} {d d₁ : ℝ} {normΛ Λ : ℂ}
    (hd₁ : d₁ < -1) (hd : d < d₁)
    (hscale : normΛ = (((-(1 / d) / 2 : ℝ) : ℂ) ^ n) * Λ) :
    ((((-2 * d : ℝ) : ℂ) ^ n) * normΛ) = Λ := by
  have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
  let s : ℂ := ((-2 * d : ℝ) : ℂ)
  let q : ℂ := ((-(1 / d) / 2 : ℝ) : ℂ)
  have hsq : s * q = 1 := by
    dsimp [s, q]
    exact_mod_cast (by field_simp [hdneg.ne] : (-2 * d) * (-(1 / d) / 2) = 1)
  calc s ^ n * normΛ = (s * q) ^ n * Λ := by rw [hscale, ← mul_assoc, ← mul_pow]
    _ = Λ := by rw [hsq, one_pow, one_mul]

private theorem cor34_final_all_parameters_aux {N n : ℕ}
    {d₀ d₁ d₂ : ℝ}
    {normEigen : ℝ → ℂ} {physEigen : ℝ → ℂ}
    (hd₀d₂ : d₀ < d₂) (hd₂d₁ : d₂ < d₁) (hd₁ : d₁ < -1)
    (hgAnalytic : ∀ d < d₂, AnalyticAt ℝ normEigen d)
    (hscale : ∀ d < d₁, ((((-2 * d : ℝ) : ℂ) ^ n) * normEigen d) = physEigen d)
    (hEqBot : ∀ᶠ d in atBot,
      physEigen d = (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n) : ℂ))
    (hbound : 2 * n ≤ N)
    (hreal : ∀ d ≤ d₀, ∃ R : ℝ, physEigen d = (R : ℂ)) :
    ∀ d ≤ d₀, (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n) : ℂ) = physEigen d := by
  let G : ℝ → ℂ := fun d => (((-2 * d : ℝ) : ℂ) ^ n) * normEigen d
  let g : ℝ → ℝ := fun d => (G d).re
  let f : ℝ → ℝ := fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)
  have hg : AnalyticOnNhd ℝ g (Iio d₂) := fun d hd => by
    have hs : AnalyticAt ℝ (fun t : ℝ => (((-2 * t : ℝ) : ℂ) ^ n)) d :=
      (cor34_final_analyticAt_ofReal (by fun_prop)).pow n
    exact (Complex.reCLM.analyticAt _).comp (hs.mul (hgAnalytic d hd))
  have hf : AnalyticOnNhd ℝ f (Iio d₂) := fun d hd =>
    cor34_analyticAt_pfRoot_transferBlock (by omega) (lt_trans (lt_trans hd hd₂d₁) hd₁)
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp hEqBot
  let dTail := min d₀ b
  have hVsub : Iio dTail ⊆ Iio d₂ := fun d hd =>
    lt_of_lt_of_le hd (le_trans (min_le_left _ _) hd₀d₂.le)
  have hEqV : EqOn f g (Iio dTail) := fun d hd => by
    have hdb : d ≤ b := (lt_of_lt_of_le hd (min_le_right _ _)).le
    have hGsource := hscale d (lt_trans (hVsub hd) hd₂d₁)
    dsimp [g, G]
    rw [hGsource, hb d hdb]
    exact (Complex.ofReal_re _).symm
  have hiden := cor34_identity_theorem_extension hf hg isPreconnected_Iio isOpen_Iio
    nonempty_Iio hVsub hEqV
  intro d hd
  have hd₂' : d < d₂ := lt_of_le_of_lt hd hd₀d₂
  have hRe : f d = (physEigen d).re := by
    rw [hiden hd₂']
    exact congrArg Complex.re (hscale d (lt_trans hd₂' hd₂d₁))
  obtain ⟨R, hR⟩ := hreal d hd
  rw [hR] at hRe ⊢
  simpa only [Complex.ofReal_re, f] using congrArg Complex.ofReal hRe

theorem cor34_final_even_all_parameters {N n r : ℕ}
    {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hd₀₁ : d₀ < d₁) (hd₁ : d₁ < -1)
    (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ d ≤ d₀,
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n) : ℂ) =
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d) := by
  obtain ⟨d₂, hd₀d₂, hd₂d₁, hregular⟩ :=
    cor34_final_even_exists_regular_cutoff hd₀₁ hpAnalytic hp hn
  have hphysical := cor34_final_even_family_eventually_physical_pfRoot
    hd₀ hp hBE hformula hPanalytic hP0 hNpos hbound hnpos hn hN hr
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] (0 : ℝ)) := by
    simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  refine cor34_final_all_parameters_aux hd₀d₂ hd₂d₁ hd₁
    (fun d hd => cor34_final_analyticAt_normalizedRegular hd₁ hpAnalytic
      (lt_trans hd hd₂d₁) (fun j => (hregular d hd j).1) (fun j => (hregular d hd j).2))
    (fun d hd => by
      have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
      have hscale := cor34_final_normalizedRegularEigenvalue_scale
        (one_div_neg.mpr hdneg) (p d)
      rw [show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hscale
      exact cor34_final_extension_cancel hd₁ hd hscale)
    (((hinv.eventually hphysical).and (Iic_mem_atBot d₀)).mono fun d ⟨hphys, hd⟩ => by
      have hdneg : d < 0 := lt_of_le_of_lt hd (lt_trans hd₀ (by norm_num))
      rwa [← hformula d hd, show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hphys)
    hbound
    (fun d hd => ⟨_, Bethe.ratio_eigenvalueRegular
      (by rw [Real.lt_sqrt (by norm_num)]; linarith [lt_of_le_of_lt hd hd₀]) (hp d hd)⟩)

theorem cor34_final_odd_all_parameters {N n q r : ℕ}
    {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hd₀₁ : d₀ < d₁) (hd₁ : d₁ < -1)
    (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ d ≤ d₀,
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n) : ℂ) =
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d)
          (⟨q - 1, by omega⟩ : Fin n) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  obtain ⟨d₂, hd₀d₂, hd₂d₁, hregular, hcenter⟩ :=
    cor34_final_odd_exists_regular_cutoff hd₀₁ hpAnalytic hp hnq
  have hphysical := cor34_final_odd_family_eventually_physical_pfRoot
    (N := N) (n := n) (q := q) (r := r) hd₀ hp hBE hformula hPanalytic hP0
    hNpos hbound hnpos hnq hN hr
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] (0 : ℝ)) := by
    simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  refine cor34_final_all_parameters_aux hd₀d₂ hd₂d₁ hd₁
    (fun d hd => cor34_final_analyticAt_normalizedZero (N := N) l hd₁ hpAnalytic
      (lt_trans hd hd₂d₁) (fun j => (hregular d hd j).1) (fun j => (hregular d hd j).2))
    (fun d hd => by
      have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
      have hInv' : 1 / (1 / d) < -1 := by rw [one_div_one_div]; exact lt_trans hd hd₁
      have hscale := cor34_final_normalizedZeroEigenvalue_scale (N := N) l hInv'
        (one_div_neg.mpr hdneg) (p d)
      rw [show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hscale
      exact cor34_final_extension_cancel hd₁ hd hscale)
    (((hinv.eventually hphysical).and (Iic_mem_atBot d₀)).mono fun d ⟨hphys, hd⟩ => by
      have hdneg : d < 0 := lt_of_le_of_lt hd (lt_trans hd₀ (by norm_num))
      rwa [← hformula d hd, show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hphys)
    hbound
    (fun d hd => ⟨_, Bethe.ratio_eigenvalueZero (N := N)
      (by rw [Real.lt_sqrt (by norm_num)]; linarith [lt_of_le_of_lt hd hd₀])
      (hp d hd) l (hcenter d (lt_of_le_of_lt hd hd₀₁))⟩)

end PottsDiscontinuity.SixVertex
