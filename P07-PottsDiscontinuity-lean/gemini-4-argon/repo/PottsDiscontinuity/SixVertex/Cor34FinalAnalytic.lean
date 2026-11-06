module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34Analytic
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

@[expose] public section

open Filter Topology Set

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_analyticAt_coordinate {n : ℕ}
    {p : ℝ → Fin n → ℝ} {d d₁ : ℝ}
    (hp : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁) (j : Fin n) :
    AnalyticAt ℝ (fun t => p t j) d := by
  have hev : AnalyticAt ℝ (fun v : Fin n → ℝ => v j) (p d) :=
    (ContinuousLinearMap.proj (R := ℝ) j).analyticAt (p d)
  exact hev.comp (hp d hd)

theorem cor34_final_analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : AnalyticAt ℝ f d) : AnalyticAt ℝ (fun t => (f t : ℂ)) d :=
  (Complex.ofRealCLM.analyticAt (f d)).comp hf

private theorem cor34_final_exists_cutoff_of_prop {n : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ} (Q : Fin n → ℝ → Prop)
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hphys : ∀ d ≤ d₀, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ Q j (p d j))
    (hopen : ∀ j, ∀ᶠ d in 𝓝 d₀, Q j (p d j)) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ Q j (p d j) := by
  have hpCont : ContinuousAt p d₀ := (hpAnalytic d₀ hd₀).continuousAt
  have hnear : ∀ᶠ d in 𝓝 d₀, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ Q j (p d j) :=
    Filter.eventually_all.2 fun j =>
      (((continuous_apply j).continuousAt.comp hpCont).eventually
        (isOpen_Ioo.mem_nhds (hphys d₀ le_rfl j).1)).and (hopen j)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min ((d₀ + d₁) / 2) (d₀ + δ / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_left _ _) (by linarith), fun d hd j => ?_⟩
  by_cases hphysical : d ≤ d₀
  · exact hphys d hphysical j
  · refine hball (Metric.mem_ball.mpr ?_) j
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith [lt_of_lt_of_le hd (min_le_right _ _)]

theorem cor34_final_even_exists_regular_cutoff {n : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hn : Even n) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ p d j ≠ 0 :=
  cor34_final_exists_cutoff_of_prop (fun _ x => x ≠ 0) hd₀ hpAnalytic
    (fun d hd j => ⟨(hp d hd).1 j, cor34_even_S_n_roots_nonzero (hp d hd) hn j⟩)
    (fun j => ((continuous_apply j).continuousAt.comp (hpAnalytic d₀ hd₀).continuousAt).eventually_ne
      (cor34_even_S_n_roots_nonzero (hp d₀ le_rfl) hn j))

theorem cor34_final_odd_center_zero_on_analytic_domain {n q : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    ∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0 :=
  cor34_identity_theorem_extension
    (fun _ hd => cor34_final_analyticAt_coordinate hpAnalytic hd _)
    (fun _ _ => analyticAt_const)
    isPreconnected_Iio isOpen_Iio nonempty_Iio
    (fun _ hd => lt_trans hd hd₀)
    (fun _ hd => cor34_odd_S_n_center_zero (hp _ hd.le) hnq)

theorem cor34_final_odd_exists_regular_cutoff {n q : ℕ}
    {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      (∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧
        (j = (⟨q - 1, by omega⟩ : Fin n) ∨ p d j ≠ 0)) ∧
      (∀ d < d₁, p d (⟨q - 1, by omega⟩ : Fin n) = 0) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hphys : ∀ d ≤ d₀, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (j = l ∨ p d j ≠ 0) :=
    fun d hd j => ⟨(hp d hd).1 j, Classical.or_iff_not_imp_left.mpr fun hj hz =>
      hj ((cor34_S_n_injective (hp d hd))
        (hz.trans (cor34_odd_S_n_center_zero (hp d hd) hnq).symm))⟩
  obtain ⟨d₂, hd₀d₂, hd₂d₁, hreg⟩ :=
    cor34_final_exists_cutoff_of_prop (fun j x => j = l ∨ x ≠ 0) hd₀ hpAnalytic hphys
      fun j => by
        by_cases hj : j = l
        · exact Filter.Eventually.of_forall fun _ => Or.inl hj
        · exact (((continuous_apply j).continuousAt.comp
            (hpAnalytic d₀ hd₀).continuousAt).eventually_ne
            ((hphys d₀ le_rfl j).2.resolve_left hj)).mono fun _ => Or.inr
  exact ⟨d₂, hd₀d₂, hd₂d₁, hreg,
    cor34_final_odd_center_zero_on_analytic_domain hd₀ hpAnalytic hp hnq⟩

private theorem cor34_final_analyticAt_z_and_M {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (j : Fin n)
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : p d j ∈ Ioo (-Real.pi) Real.pi) (hnonzero : p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedL (1 / t) (p t j)) d ∧
      AnalyticAt ℝ (fun t => cor34_normalizedM (1 / t) (p t j)) d := by
  have hd0 : d ≠ 0 := ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num)))
  have hepsR : AnalyticAt ℝ (fun t : ℝ => 1 / t) d := analyticAt_const.div analyticAt_id hd0
  have hhalfC : AnalyticAt ℝ (fun t : ℝ => ((-(1 / t) / 2 : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal (by fun_prop)
  have hcoefC : AnalyticAt ℝ (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal (analyticAt_const.sub hepsR)
  have hpjC := cor34_final_analyticAt_ofReal (cor34_final_analyticAt_coordinate hpAnalytic hd j)
  have hZ : AnalyticAt ℝ (fun t : ℝ => BetheAnsatz.z (p t j)) d :=
    analyticAt_cexp.restrictScalars.comp (analyticAt_const.mul hpjC)
  have hden : AnalyticAt ℝ (fun t : ℝ => 1 - BetheAnsatz.z (p t j)) d :=
    analyticAt_const.sub hZ
  have hdenne : 1 - BetheAnsatz.z (p d j) ≠ 0 :=
    sub_ne_zero.mpr (BetheAnsatz.z_ne_one hrange hnonzero).symm
  refine ⟨?_, ?_⟩
  · convert hhalfC.add (hcoefC.mul (hZ.div hden hdenne)) using 1
    ext t; simp [cor34_normalizedL, div_eq_mul_inv]; ring
  · convert hhalfC.sub (hcoefC.div hden hdenne) using 1
    ext t; simp [cor34_normalizedM]

theorem cor34_final_analyticAt_normalizedRegular {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hnonzero : ∀ j, p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedRegularEigenvalue (1 / t) (p t)) d := by
  have hLM := fun j => cor34_final_analyticAt_z_and_M j hd₁ hpAnalytic hd (hrange j) (hnonzero j)
  convert (Finset.univ.analyticAt_fun_prod fun j _ => (hLM j).1).add
    (Finset.univ.analyticAt_fun_prod fun j _ => (hLM j).2) using 1
  ext t; simp [cor34_normalizedRegularEigenvalue]

private theorem cor34_final_analyticAt_derivativeCorrection {n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (j : Fin n) :
    AnalyticAt ℝ (fun t => cor34_derivativeCorrection (1 / t) (p t j)) d := by
  have hd0 : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
  have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d := analyticAt_const.div analyticAt_id hd0.ne
  have hpj := cor34_final_analyticAt_coordinate hpAnalytic hd j
  have harg : (1 / d) * (1 + Real.cos (p d j)) - 2 < 0 := by
    nlinarith [one_div_neg.mpr hd0, Real.neg_one_le_cos (p d j)]
  have hdenPos : 0 < ((1 / d) * (1 + Real.cos (p d j)) - 2) ^ 2 +
      (1 / d) ^ 2 * (Real.sin (p d j)) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero harg.ne) (by positivity)
  exact (by fun_prop : AnalyticAt ℝ (fun t : ℝ =>
    2 * (1 / t) * ((1 / t) * (1 + Real.cos (p t j)) - 2)) d).div
    (by fun_prop) hdenPos.ne'

theorem cor34_final_analyticAt_normalizedZero {N n : ℕ}
    {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (l : Fin n)
    (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hgood : ∀ j, j = l ∨ p d j ≠ 0) :
    AnalyticAt ℝ
      (fun t => cor34_normalizedZeroEigenvalue (N := N) (1 / t) (p t) l) d := by
  have hd0 : d ≠ 0 := ne_of_lt (lt_trans hd (lt_trans hd₁ (by norm_num)))
  have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d := analyticAt_const.div analyticAt_id hd0
  have hcoefC : AnalyticAt ℝ (fun t : ℝ => ((1 - 1 / t : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal (analyticAt_const.sub heps)
  have hminusC : AnalyticAt ℝ (fun t : ℝ => ((-(1 / t) : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal (by fun_prop)
  have hsumC : AnalyticAt ℝ
      (fun t : ℝ => (((N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection (1 / t) (p t j)) : ℝ) : ℂ)) d :=
    cor34_final_analyticAt_ofReal (analyticAt_const.add
      ((Finset.univ.erase l).analyticAt_fun_sum fun j _ =>
        analyticAt_const.add (cor34_final_analyticAt_derivativeCorrection hd₁ hpAnalytic hd j)))
  have hprod := (Finset.univ.erase l).analyticAt_fun_prod fun j hj =>
    (cor34_final_analyticAt_z_and_M j hd₁ hpAnalytic hd (hrange j)
      ((hgood j).resolve_left (Finset.mem_erase.mp hj).1)).2
  convert (hminusC.add (hcoefC.mul hsumC)).mul hprod using 1
  ext t; simp [cor34_normalizedZeroEigenvalue]

end PottsDiscontinuity.SixVertex
