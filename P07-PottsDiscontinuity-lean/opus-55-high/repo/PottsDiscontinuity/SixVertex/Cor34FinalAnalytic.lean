module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34Analytic
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Corollary 3.4: analytic Bethe branches near the endpoint -/

public section

open Filter Topology Set

namespace PottsDiscontinuity.SixVertex

theorem cor34_final_analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : AnalyticAt ℝ f d) : AnalyticAt ℝ (fun t => (f t : ℂ)) d :=
  (Complex.ofRealCLM.analyticAt _).comp hf

/-- All roots outside `Z` stay nonzero, and all roots stay in the principal momentum interval,
on a slightly larger interval than the physical range. -/
theorem cor34_final_exists_regular_cutoff {n : ℕ} {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (Z : Fin n → Prop) (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hZ : ∀ d ≤ d₀, ∀ j, Z j ∨ p d j ≠ 0) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧
      ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (Z j ∨ p d j ≠ 0) := by
  have hcoordinate (j : Fin n) :
      ∀ᶠ d in 𝓝 d₀, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (Z j ∨ p d j ≠ 0) := by
    have hcont := (continuous_apply j).continuousAt.comp ((hpAnalytic d₀ hd₀).continuousAt)
    refine (hcont.eventually (isOpen_Ioo.mem_nhds ((hp d₀ le_rfl).1 j))).and ?_
    rcases hZ d₀ le_rfl j with h | h
    · exact .of_forall fun _ => .inl h
    · exact (hcont.eventually_ne h).mono fun _ => .inr
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (eventually_all.2 hcoordinate)
  refine ⟨min ((d₀ + d₁) / 2) (d₀ + δ / 2), by grind, by grind, fun d hd j => ?_⟩
  by_cases hphysical : d ≤ d₀
  · exact ⟨(hp d hphysical).1 j, hZ d hphysical j⟩
  · exact hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_right ((d₀ + d₁) / 2) (d₀ + δ / 2)]) j

section
variable {n : ℕ} {d d₁ : ℝ} {p : ℝ → Fin n → ℝ} (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁)
include hd₁ hpAnalytic hd

theorem cor34_final_analyticAt_LM (j : Fin n) (hj : p d j ∈ Ioo (-Real.pi) Real.pi)
    (h0 : p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedL (1 / t) (p t j)) d ∧
      AnalyticAt ℝ (fun t => cor34_normalizedM (1 / t) (p t j)) d := by
  have hd0 : d ≠ 0 := by linarith
  have := cor34_final_analyticAt_ofReal (analyticAt_pi_iff.1 (hpAnalytic d hd) j)
  have hz : AnalyticAt ℝ (fun t => BetheAnsatz.z (p t j)) d :=
    analyticAt_cexp.restrictScalars.comp (by fun_prop)
  have hden : AnalyticAt ℝ (fun t => 1 - BetheAnsatz.z (p t j)) d := by fun_prop
  have hne := sub_ne_zero.2 (BetheAnsatz.z_ne_one hj h0).symm
  have h1 := cor34_final_analyticAt_ofReal (d := d) (f := fun t => -(1 / t) / 2) (by fun_prop)
  have h2 := cor34_final_analyticAt_ofReal (d := d) (f := fun t => 1 - 1 / t) (by fun_prop)
  exact ⟨h1.add (h2.mul (hz.div hden hne)) |>.congr (.of_forall fun t => by
    simp [cor34_normalizedL, mul_div_assoc]), h1.sub (h2.div hden hne)⟩

/-- The normalized regular Bethe eigenvalue is analytic wherever all momenta avoid zero and
remain in the principal interval. -/
theorem cor34_final_analyticAt_normalizedRegular (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hnonzero : ∀ j, p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedRegularEigenvalue (1 / t) (p t)) d :=
  (Finset.univ.analyticAt_fun_prod fun j _ =>
    (cor34_final_analyticAt_LM hd₁ hpAnalytic hd j (hrange j) (hnonzero j)).1).add
  (Finset.univ.analyticAt_fun_prod fun j _ =>
    (cor34_final_analyticAt_LM hd₁ hpAnalytic hd j (hrange j) (hnonzero j)).2)

/-- The odd normalized zero-root expression is analytic after deleting its centered root. -/
theorem cor34_final_analyticAt_normalizedZero {N : ℕ} (l : Fin n)
    (hrange : ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi)
    (hgood : ∀ j, j = l ∨ p d j ≠ 0) :
    AnalyticAt ℝ
      (fun t => cor34_normalizedZeroEigenvalue (N := N) (1 / t) (p t) l) d := by
  have hd0 : d ≠ 0 := by linarith
  have hcorr (j : Fin n) : AnalyticAt ℝ (fun t => cor34_derivativeCorrection (1 / t) (p t j)) d := by
    have := analyticAt_pi_iff.1 (hpAnalytic d hd) j
    have hε := one_div_neg.mpr (show d < 0 by linarith)
    have : 0 < ((1 / d) * (1 + Real.cos (p d j)) - 2) ^ 2 +
        (1 / d) ^ 2 * (Real.sin (p d j)) ^ 2 := by
      nlinarith [show (1 / d) * (1 + Real.cos (p d j)) - 2 < 0 by
        nlinarith [Real.neg_one_le_cos (p d j)]]
    unfold cor34_derivativeCorrection
    fun_prop (disch := first | assumption | exact this.ne')
  have h1 := cor34_final_analyticAt_ofReal (d := d) (f := fun t => -(1 / t)) (by fun_prop)
  have h2 := cor34_final_analyticAt_ofReal (d := d) (f := fun t => 1 - 1 / t) (by fun_prop)
  have h3 := cor34_final_analyticAt_ofReal (f := fun t => (N : ℝ) - 1 +
        ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection (1 / t) (p t j))) (by fun_prop)
  exact ((h1.add (h2.mul h3)).mul ((Finset.univ.erase l).analyticAt_fun_prod fun j hj =>
    (cor34_final_analyticAt_LM hd₁ hpAnalytic hd j (hrange j)
      ((hgood j).resolve_left (Finset.ne_of_mem_erase hj))).2)).congr
    (.of_forall fun t => by simp [cor34_normalizedZeroEigenvalue])
end

end PottsDiscontinuity.SixVertex
