module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34Analytic
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Corollary 3.4: analytic Bethe branches near the endpoint -/

@[expose] public section

open Filter Topology Set

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_analyticAt_coordinate {n : ℕ}
    {p : ℝ → Fin n → ℝ} {d d₁ : ℝ}
    (hp : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁) (j : Fin n) :
    AnalyticAt ℝ (fun t => p t j) d := by
  have hev : AnalyticAt ℝ (fun v  => v j) (p d) := by
    convert (ContinuousLinearMap.proj (R := ℝ) j).analyticAt (p d) using 1
    
    rfl
  exact hev.comp (hp d hd)

theorem cor34_final_analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : AnalyticAt ℝ f d) : AnalyticAt ℝ (fun t => (f t : ℂ)) d := AnalyticAt.comp (ContinuousLinearMap.analyticAt Complex.ofRealCLM (f d)) hf

/-- The branch has no zero roots and stays in the principal momentum interval on a slightly
larger interval than the physical range, when the root count is even. -/
theorem cor34_final_even_exists_regular_cutoff {n : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hn : Even n) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0 := by
  have hp₀  := hp d₀ le_rfl
  
  
  
   
  
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.2  fun j => by
                                                                                have hcont  :=
                                                                                  (continuous_apply j).continuousAt.comp ((hpAnalytic d₀ hd₀).continuousAt)
                                                                                
                                                                                exact (hcont.eventually (isOpen_Ioo.mem_nhds (hp₀.1 j))).and (hcont.eventually_ne ((fun j => cor34_even_S_n_roots_nonzero hp₀ hn j) j)))
  
  
  
  refine ⟨ min ((d₀ + d₁) / 2) (d₀ + δ / 2) ,  by
                 apply lt_min
                 · linarith
                 · linarith ,  lt_of_le_of_lt (min_le_left _ _) (by linarith) , ?_⟩
  intro d hd j
  by_cases hphysical : d ≤ d₀
  · have hS := hp d hphysical
    exact ⟨hS.1 j, cor34_even_S_n_roots_nonzero hS hn j⟩
  · 
    have hdu  := lt_of_lt_of_le hd (min_le_right _ _)
    
    exact hball (Metric.mem_ball.mpr (by
                                        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (lt_of_not_ge hphysical))]
                                        linarith)) j

section

variable {n q : ℕ} {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ} (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
include hd₀ hpAnalytic hp hnq

/-- The odd analytic family keeps its centered zero root identically zero. -/
theorem cor34_final_odd_center_zero_on_analytic_domain  :
    ∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0 := by
  let l : Fin n := ⟨q - 1, by omega⟩
  
  
  
  
  intro d hd
  simpa  using (cor34_identity_theorem_extension (fun d hd => cor34_final_analyticAt_coordinate hpAnalytic hd l) (fun d hd => analyticAt_const)
                     isPreconnected_Iio isOpen_Iio nonempty_Iio
                     (fun d hd => lt_trans hd hd₀) (fun d hd => cor34_odd_S_n_center_zero (hp d hd.le) hnq)) hd

/-- In the odd case all noncentral roots stay nonzero, and all roots stay in the principal
momentum interval, on a slightly larger interval than the physical range. -/
theorem cor34_final_odd_exists_regular_cutoff  :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      (∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧
        (j = (⟨q - 1, by omega⟩ : Fin n) ∨ p d j ≠ 0)) ∧
       ∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0  := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hp₀  := hp d₀ le_rfl
  
  have hnonzero₀ : ∀ j, j = l ∨ p d₀ j ≠ 0 := by
    intro j
    by_cases hj : j = l
    · exact Or.inl hj
    · right
      intro h
      apply hj
      exact (cor34_S_n_injective hp₀) (h.trans (cor34_odd_S_n_center_zero hp₀ hnq).symm)
  
  
  have hnear  :=
    Filter.eventually_all.2  fun j => by
                               have hcont  :=
                                 (continuous_apply j).continuousAt.comp  (hpAnalytic d₀ hd₀).continuousAt 
                               
                               have hroot : ∀ᶠ d in 𝓝 d₀, j = l ∨ p d j ≠ 0 := by
                                 by_cases hj : j = l
                                 · simp_all
                                 · exact (hcont.eventually_ne (by
                                     grind)).mono  fun _ hne => Or.inr hne 
                               exact (hcont.eventually (isOpen_Ioo.mem_nhds (hp₀.1 j))).and hroot 
  
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  
  
  
  
  refine ⟨ min ((d₀ + d₁) / 2) (d₀ + δ / 2) ,  by
                 apply lt_min
                 · linarith
                 · linarith ,  lt_of_le_of_lt (min_le_left _ _) (by linarith) , ?_,  cor34_final_odd_center_zero_on_analytic_domain hd₀ hpAnalytic hp hnq ⟩
  intro d hd j
  by_cases hphysical : d ≤ d₀
  · have hS := hp d hphysical
    
    exact ⟨hS.1 j,  by
                      by_cases hj : j = l
                      · exact Or.inl hj
                      · right
                        intro hz
                        apply hj
                        exact (cor34_S_n_injective hS) (hz.trans (cor34_odd_S_n_center_zero hS hnq).symm) ⟩
  · 
    have hdu  := lt_of_lt_of_le hd (min_le_right _ _)
    
    exact hball (Metric.mem_ball.mpr (by
                                        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (lt_of_not_ge hphysical))]
                                        linarith)) j

end

section

variable {n : ℕ} {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
include hd₁ hpAnalytic hd

/-- The normalized regular Bethe eigenvalue is analytic wherever all momenta avoid zero and
remain in the principal interval. -/
theorem cor34_final_analyticAt_normalizedRegular 
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hnonzero : ∀ j, p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedRegularEigenvalue (1 / t) (p t)) d := by
  have hepsR : AnalyticAt ℝ (fun t  => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hhalfR : AnalyticAt ℝ (fun t  => -(1 / t) / 2) d := by
    fun_prop
  have hhalfC  :=
    cor34_final_analyticAt_ofReal hhalfR
  have hcoefR : AnalyticAt ℝ (fun t  => 1 - 1 / t) d :=
    analyticAt_const.sub hepsR
  have hcoefC  :=
    cor34_final_analyticAt_ofReal hcoefR
  have hZ (j : Fin n) :
      AnalyticAt ℝ (fun t  => BetheAnsatz.z (p t j)) d := AnalyticAt.comp (AnalyticAt.restrictScalars analyticAt_cexp)
                                                               (AnalyticAt.fun_mul analyticAt_const
                                                                 (cor34_final_analyticAt_ofReal (cor34_final_analyticAt_coordinate hpAnalytic hd j)))
  
  have hdenne (j : Fin n) : 1 - BetheAnsatz.z (p d j) ≠ 0 := by
    have hz := BetheAnsatz.z_ne_one (hrange j) (hnonzero j)
    grind
  have hL (j : Fin n) :
      AnalyticAt ℝ (fun t  => cor34_normalizedL (1 / t) (p t j)) d := by
    simp only [cor34_normalizedL]
    fun_prop (disch := aesop)
  have hM (j : Fin n) :
      AnalyticAt ℝ (fun t  => cor34_normalizedM (1 / t) (p t j)) d := by
    simp only [cor34_normalizedM]
    fun_prop (disch := aesop)
  have hprodL := Finset.univ.analyticAt_fun_prod  fun j _ => hL j 
  have hprodM := Finset.univ.analyticAt_fun_prod  fun j _ => hM j 
  convert hprodL.add hprodM using 1
  ext t
  simp [cor34_normalizedRegularEigenvalue]

private theorem cor34_final_analyticAt_derivativeCorrection 
    (j : Fin n) :
    AnalyticAt ℝ (fun t => cor34_derivativeCorrection (1 / t) (p t j)) d := by
  have heps : AnalyticAt ℝ (fun t  => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hpj := cor34_final_analyticAt_coordinate hpAnalytic hd j
  
  
  have hnum : AnalyticAt ℝ
      (fun t  => 2 * (1 / t) * ( 1 / t  * (1 + Real.cos (p t j)) - 2)) d := by
    fun_prop
  have hden : AnalyticAt ℝ
      (fun t  => ( 1 / t  * (1 + Real.cos (p t j)) - 2) ^ 2 +
        (1 / t) ^ 2 *  Real.sin (p t j)  ^ 2) d := by
    fun_prop
  have harg :  1 / d  * (1 + Real.cos (p d j)) - 2 < 0 := by
    have hε  := one_div_neg.mpr (lt_trans hd (lt_trans hd₁ (by norm_num)))
    have hcos₀ : 0 ≤ 1 + Real.cos (p d j) := by
      linarith [Real.neg_one_le_cos (p d j)]
    nlinarith
  
  have hquot := hnum.div hden (ne_of_gt (by
                                           nlinarith))
  convert hquot using 1
  ext t
  simp [cor34_derivativeCorrection]

end

/-- The odd normalized zero-root expression is analytic after deleting its centered root. -/
theorem cor34_final_analyticAt_normalizedZero {N n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (l : Fin n)
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hgood : ∀ j, j = l ∨ p d j ≠ 0) :
    AnalyticAt ℝ
      (fun t => cor34_normalizedZeroEigenvalue (N := N) (1 / t) (p t) l) d := by
  have heps : AnalyticAt ℝ (fun t  => 1 / t) d :=
    analyticAt_const.div analyticAt_id
      (ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num))))
  have hhalfR : AnalyticAt ℝ (fun t  => -(1 / t) / 2) d := by fun_prop
  have hhalfC  :=
    cor34_final_analyticAt_ofReal hhalfR
  have hcoefR : AnalyticAt ℝ (fun t  => 1 - 1 / t) d :=
    analyticAt_const.sub heps
  have hcoefC  :=
    cor34_final_analyticAt_ofReal hcoefR
  have hZ (j : Fin n) :
      AnalyticAt ℝ (fun t  => BetheAnsatz.z (p t j)) d := AnalyticAt.comp (AnalyticAt.restrictScalars analyticAt_cexp)
                                                               (AnalyticAt.fun_mul analyticAt_const
                                                                 (cor34_final_analyticAt_ofReal (cor34_final_analyticAt_coordinate hpAnalytic hd j)))
  
  have hdenne (j : Fin n) (hj : j ≠ l) :
      1 - BetheAnsatz.z (p d j) ≠ 0 := fun h => (BetheAnsatz.z_ne_one (hrange j) (by
                                                                                      grind)) (sub_eq_zero.mp h).symm
  have hM (j : Fin n) (hj : j ∈ Finset.univ.erase l) :
      AnalyticAt ℝ (fun t  => cor34_normalizedM (1 / t) (p t j)) d := by
    simp only [cor34_normalizedM]
    fun_prop (disch := aesop)
  have hcorr (j : Fin n)  :=
    cor34_final_analyticAt_derivativeCorrection hd₁ hpAnalytic hd j
  have hsum : AnalyticAt ℝ
      (fun t  =>  N  - 1 +
        ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection (1 / t) (p t j))) d := by
    fun_prop
  
  have hminusR : AnalyticAt ℝ (fun t  => -(1 / t)) d := by fun_prop
  
  
  have hprod := (Finset.univ.erase l).analyticAt_fun_prod
     hM 
  have htotal := ((cor34_final_analyticAt_ofReal hminusR).add (hcoefC.mul (cor34_final_analyticAt_ofReal hsum))).mul hprod
  convert htotal using 1
  ext t
  simp [cor34_normalizedZeroEigenvalue]

end PottsDiscontinuity.SixVertex
