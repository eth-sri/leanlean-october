module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Compact smooth primitives of zero-mean tests on the real line -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A smooth compactly supported real test of integral zero has a smooth compact primitive. -/
theorem bellman_exists_test_primitive (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hm : (∫ x, φ x) = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ deriv ψ = φ := by
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨a₀, _, hmin⟩ := hc.exists_isMinOn hn continuousOn_id
    obtain ⟨b₀, _, hmax⟩ := hc.exists_isMaxOn hn continuousOn_id
    let a := a₀ - 1
    let b := b₀ + 1
    let ψ := fun t => ∫ x in a..t, φ x
    have hleft : ∀ t : ℝ, t < a → ψ t = 0 := by
      intro t ht
      rw [show ψ t = ∫ x in a..t, φ x from rfl,
        intervalIntegral.integral_of_ge ht.le]
      apply neg_eq_zero.mpr
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hl : a₀ ≤ x := hmin hs
      have hr := hx.2
      dsimp [a] at hr
      linarith
    have hright : ∀ t : ℝ, b < t → ψ t = 0 := by
      intro t ht
      change (∫ x in a..t, φ x) = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset]
      · exact hm
      · intro x hx
        have hs := subset_tsupport φ hx
        have hl := hmin hs
        have hr := hmax hs
        grind
    have hsupp : Function.support ψ ⊆ Icc a b := by
      intro t ht
      rcases lt_or_ge t a with hta | hta
      · aesop
      · have htb : t ≤ b := by
          by_contra hn
          bound
        exact ⟨hta, htb⟩
    have hts := closure_minimal hsupp isClosed_Icc
    have hderiv : deriv ψ = φ := by
      funext t
      apply hφ.continuous.deriv_integral
    refine ⟨ψ, ?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts, hderiv⟩
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨?_, ?_⟩
    · intro t
      exact (hφ.continuous.integral_hasStrictDerivAt a t).hasDerivAt.differentiableAt
    · rw [hderiv]
      exact hφ
  · have hz : φ = 0 := by
      funext t
      exact image_eq_zero_of_notMem_tsupport (fun ht => hn ⟨t, ht⟩)
    aesop

end HypoellipticAleksandrov.KineticAleksandrov
