module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34FinalAnalytic
public import PottsDiscontinuity.SixVertex.Cor34FinalFamily

/-! # Corollary 3.4: identify the Theorem 2.3 family with the Perron root -/

@[expose] public section

open Filter Topology Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_even_extension_eq_source {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hd : d < d₁) :
      ((-2 * d : ℝ) : ℂ) ^ n  *
        cor34_normalizedRegularEigenvalue (1 / d) (p d)  =
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d) := by
  have hdneg : d < 0 := by
                          nlinarith
  
  have hrecip2 : 2 / (1 / d) = 2 * d := by
    field_simp 
  
  have hscale := cor34_final_normalizedRegularEigenvalue_scale
    (ε := 1 / d) (one_div_neg.mpr hdneg) (p d)
  rw [hrecip2] at hscale
  let s  :=  (-2 * d : ℝ) 
  let q : ℂ :=  (-(1 / d) / 2 : ℝ) 
  have hsqR :  -2 * d  * (-(1 / d) / 2) = 1 := by
    field_simp [ne_of_lt hdneg]
  have hsq : s * q = 1 := by
    dsimp [s, q]
    exact_mod_cast hsqR
  calc
    _ = s ^ n * cor34_normalizedRegularEigenvalue (1 / d) (p d) := rfl
    _ = s ^ n * (q ^ n *
          BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d)) := by
      rw [hscale]
    _ = (s * q) ^ n *
          BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d) := by
      ring
    _ = _ := by rw [hsq]; simp

private theorem cor34_final_odd_extension_eq_source {N n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (l : Fin n)
    (hd₁ : d₁ < -1) (hd : d < d₁) :
      ((-2 * d : ℝ) : ℂ) ^ n  *
        cor34_normalizedZeroEigenvalue (N := N) (1 / d) (p d) l  =
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l := by
  have hdneg : d < 0 := by
                          nlinarith
  have hrecip : 1 / (1 / d) = d := by field_simp 
  have hrecip2 : 2 / (1 / d) = 2 * d := by
    field_simp 
  
  
  have hscale := cor34_final_normalizedZeroEigenvalue_scale
    (N := N) (n := n) l (by rw [hrecip]; exact lt_trans hd hd₁) (one_div_neg.mpr hdneg) (p d)
  rw [hrecip2] at hscale
  let s  :=  (-2 * d : ℝ) 
  let q : ℂ :=  (-(1 / d) / 2 : ℝ) 
  have hsqR :  -2 * d  * (-(1 / d) / 2) = 1 := by
    field_simp [ne_of_lt hdneg]
  have hsq : s * q = 1 := by
    dsimp [s, q]
    exact_mod_cast hsqR
  calc
    _ = s ^ n * cor34_normalizedZeroEigenvalue (N := N) (1 / d) (p d) l := rfl
    _ = s ^ n * (q ^ n *
          BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l) := by
      rw [hscale]
    _ = (s * q) ^ n *
          BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l := by
      ring
    _ = _ := by rw [hsq]; simp

/-- Even-parity Corollary 3.4 for the analytic Theorem 2.3 family. -/
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
  let G  := fun d =>   (-2 * d : ℝ)  ^ n  *
    cor34_normalizedRegularEigenvalue (1 / d) (p d)
  let g  := fun d => (G d).re
  let f  := fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)
  have hg : AnalyticOnNhd ℝ g (Iio d₂) := by
    intro d hd
    
    have hsR : AnalyticAt ℝ (fun t  => -2 * t) d := by fun_prop
    have hsC  :=
      cor34_final_analyticAt_ofReal hsR
    
    
    
    exact (Complex.reCLM.analyticAt _).comp ((hsC.pow n).mul (cor34_final_analyticAt_normalizedRegular hd₁ hpAnalytic
                                                                   (lt_trans hd hd₂d₁) (fun j => (hregular d hd j).1)
                                                                    fun j => (hregular d hd j).2 ))
  
  
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] 0) := by
    simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  
  obtain ⟨b, hb⟩ :=  Filter.eventually_atBot.mp (hinv.eventually (cor34_final_even_family_eventually_physical_pfRoot
                                                                                   hd₀ hp hBE hformula hPanalytic hP0 hNpos hbound hnpos hn hN hr)) 
  
  
  
  have hEqV : EqOn f g (Iio (min d₀ b)) := by
    intro d hd
    
    
    have hrecip2 : 2 / (1 / d) = 2 * d := by
      linarith
    have hraw := hb d (le_of_lt (lt_of_lt_of_le hd (min_le_right _ _)))
    rw [← hformula d (le_of_lt (lt_of_lt_of_le hd (min_le_left _ _))), hrecip2] at hraw
    
    
    
    
    
    calc
      f d = (BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d)).re := (congrArg Complex.re hraw).symm
      _ = (G d).re := (congrArg Complex.re (cor34_final_even_extension_eq_source
                                              (n := n) (p := p) hd₁ (lt_trans hd (lt_of_le_of_lt (min_le_left _ _) hd₀₁)))).symm
  
  have hiden := cor34_identity_theorem_extension (by
                                                    intro d hd
                                                    exact cor34_analyticAt_pfRoot_transferBlock (by omega)
                                                      (lt_trans (lt_trans hd hd₂d₁) hd₁)) hg isPreconnected_Iio isOpen_Iio
    nonempty_Iio (by
                    grind) hEqV
  intro d hd
  have hd₂'  := lt_of_le_of_lt hd hd₀d₂
  have hidenD := hiden hd₂'
  have hGsource := cor34_final_even_extension_eq_source
    (n := n) (p := p) hd₁ (lt_trans hd₂' hd₂d₁)
  
  have hc : 2 < Real.sqrt (2 - 2 * d) := by
    
    
    rw [Real.lt_sqrt (by norm_num )]
    nlinarith 
  have hratio := Bethe.ratio_eigenvalueRegular hc (hp d hd)
  have hLambda : f d = 2 * ∏ j, ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d))
      (BetheAnsatz.z (p d j))‖ := by
    calc
      f d = (BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d)).re :=  by
                                                                                   grind 
      _ = 2 * ∏ j, ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d))
          (BetheAnsatz.z (p d j))‖ := by
        have hprod : (∏ j : Fin n,
            ( ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d))
              (BetheAnsatz.z (p d j))‖  : ℂ)).re =
              ∏ j : Fin n, ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d))
                (BetheAnsatz.z (p d j))‖ := by
          norm_cast
        simpa [hprod] using congrArg Complex.re hratio
  rw [hratio]
  simpa [f] using congrArg Complex.ofReal hLambda

/-- Odd-parity Corollary 3.4, using the centered zero-root eigenvalue formula. -/
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
  let G  := fun d =>   (-2 * d : ℝ)  ^ n  *
    cor34_normalizedZeroEigenvalue (N := N) (1 / d) (p d) l
  let g  := fun d => (G d).re
  let f  := fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)
  have hg : AnalyticOnNhd ℝ g (Iio d₂) := by
    intro d hd
    
    have hreg := cor34_final_analyticAt_normalizedZero (N := N) l hd₁ hpAnalytic
      (lt_trans hd hd₂d₁) (fun j => (hregular d hd j).1) (by
                                                                                                   aesop)
    have hsR : AnalyticAt ℝ (fun t  => -2 * t) d := by fun_prop
    have hsC  :=
      cor34_final_analyticAt_ofReal hsR
    
    have hG  := (hsC.pow n).mul hreg
    
    exact (Complex.reCLM.analyticAt _).comp hG
  
  
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] 0) := by
    simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  
  obtain ⟨b, hb⟩ :=  Filter.eventually_atBot.mp (hinv.eventually (cor34_final_odd_family_eventually_physical_pfRoot
                                                                                   (N := N) (n := n) (q := q) (r := r) hd₀ hp hBE hformula hPanalytic hP0
                                                                                   hNpos hbound hnpos hnq hN hr)) 
  
  
  
  have hEqV : EqOn f g (Iio (min d₀ b)) := by
    intro d hd
    
    
    have hrecip2 : 2 / (1 / d) = 2 * d := by
      linarith
    have hraw := hb d (le_of_lt (lt_of_lt_of_le hd (min_le_right _ _)))
    rw [← hformula d (le_of_lt (lt_of_lt_of_le hd (min_le_left _ _))), hrecip2] at hraw
    
    
    
    
    
    calc
      f d = (BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l).re := (congrArg Complex.re hraw).symm
      _ = (G d).re := (congrArg Complex.re (cor34_final_odd_extension_eq_source (N := N) (n := n)
                                              (p := p) l hd₁ (lt_trans hd (lt_of_le_of_lt (min_le_left _ _) hd₀₁)))).symm
  
  have hiden := cor34_identity_theorem_extension (by
                                                    intro d hd
                                                    exact cor34_analyticAt_pfRoot_transferBlock (by omega)
                                                      (lt_trans (lt_trans hd hd₂d₁) hd₁)) hg isPreconnected_Iio isOpen_Iio
    nonempty_Iio (by
                    grind) hEqV
  intro d hd
  have hd₂'  := lt_of_le_of_lt hd hd₀d₂
  have hidenD := hiden hd₂'
  have hGsource := cor34_final_odd_extension_eq_source (N := N) (n := n)
    (p := p) l hd₁ (lt_trans hd₂' hd₂d₁)
  have hRe : f d =
      (BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l).re := by
    grind
  have hc : 2 < Real.sqrt (2 - 2 * d) := by
    
    have hsquare : 4 < 2 - 2 * d := by linarith
    rw [Real.lt_sqrt (by norm_num )]
    nlinarith 
  
  have hratio := Bethe.ratio_eigenvalueZero (N := N) (n := n)
    hc (hp d hd) l (hcenter d (lt_of_le_of_lt hd hd₀₁))
  let R  :=
    (2 +  Real.sqrt (2 - 2 * d)  ^ 2 * ( N  - 1) +
       Real.sqrt (2 - 2 * d)  ^ 2 *
        ∑ j ∈ Finset.univ.erase l,
          deriv
            (fun t => PottsDiscontinuity.Bethe.theta
              (BetheAnsatz.anisotropy (Real.sqrt (2 - 2 * d))) t (p d j)) 0) *
      ∏ j ∈ Finset.univ.erase l,
        ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d))
          (BetheAnsatz.z (p d j))‖
  have hratioRe :
      (BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l).re = R := congrArg Complex.re hratio
  
  have hratio' : BetheAnsatz.eigenvalueZero N
      (Real.sqrt (2 - 2 * d)) (p d)  ⟨q - 1, by omega⟩  = (R ) := by
    simpa [R] using hratio
  rw [hratio']
  simpa [f] using congrArg Complex.ofReal (hRe.trans hratioRe)

end PottsDiscontinuity.SixVertex
