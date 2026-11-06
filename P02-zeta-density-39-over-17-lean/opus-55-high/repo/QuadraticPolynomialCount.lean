module
public import QuadraticHeightBudget
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Filter Finset
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- Full perturbed detecting-length window for the actual bounded polynomial.
This theorem is unconditional; coefficient-one zero detection is a separate
remaining analytic step. -/
theorem quadratic_polynomial_count_loss {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hδ : 0 < δ)
    (hδ' : δ ≤ (1-3*a/2)/2) (hsmall : 9*δ < a*(4*σ-3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ N t₀ : ℝ, T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+51*δ) := by
  pm_69 A hA hbound finite_quadratic_large_value_second MathCollab.Density.comparisonCutoff hδ
  refine ⟨1+(1+6*A)^3,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),quadratic_diagonal_budget hw hA hδ.le hsmall]
    with T hT hsink
  intro N t₀ hlo hhi b hb W hW hsep hlarge
  have hTp : 0 < T := by linarith
  have hN1 : 1 ≤ N := (Real.one_le_rpow hT.le (show 0 ≤ a by linarith [hw.a_low])).trans hlo
  have hNp : 0 < N := by linarith
  have hV : 0 < N^σ*T^(-2*δ) := by positivity
  let p := 3*a*(1-σ)
  have hP : 0 < T^p := by positivity
  obtain ⟨L,hNL,hLT,hbase,hfirst,hsecond⟩ := quadratic_monomial_budgets hw hδ.le hδ' hT hNp hlo hhi
  have hLp : 0 < L := hNp.trans_le hNL
  by_cases hR : (W.card:ℝ) ≤ T^p
  · have hp : T^p ≤ T^(p+51*δ) := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    exact (hR.trans hp).trans (by
      have hC : 1 ≤ 1+(1+6*A)^3 := by
        have hh : 0 ≤ (1+6*A)^3 := by positivity
        linarith only [hh]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ T^(p+51*δ)))
  · have hs : T^p ≤ (W.card:ℝ) := (le_of_not_ge hR)
    have hquad := hbound T t₀ N L hT hN1 hNL hLT b hb W (N^σ*T^(-2*δ)) hV.le hW hlarge hsep
    have hh := quadratic_scalar_absorption hNp hLp hTp hV hP hs
      (Real.one_le_rpow hT.le (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow hT.le hδ.le) hA hquad (hsink.2 N hNp hlo)
      hbase hfirst hsecond
    have he : (T^δ)^3*(T^(16*δ))^3*T^p=T^(p+51*δ) := by
      rw [← Real.rpow_natCast (T^δ) 3,← Real.rpow_mul hTp.le,
        ← Real.rpow_natCast (T^(16*δ)) 3,← Real.rpow_mul hTp.le,
        ← Real.rpow_add hTp,← Real.rpow_add hTp]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (1+6*A)^3*(T^δ)^3*(T^(16*δ))^3*T^p := hh
      _ = (1+6*A)^3*T^(p+51*δ) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Montgomery.RationalMoment
