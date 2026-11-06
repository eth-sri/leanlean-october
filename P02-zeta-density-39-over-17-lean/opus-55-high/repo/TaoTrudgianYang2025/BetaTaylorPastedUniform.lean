module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaTaylorPastedTransitionBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Uniform finite jets of the constructed global Taylor extension

The five-region proof keeps every transition boundary. The constant is
chosen before the moving interval, width and original function. Only the
fixed observation distance D and requested finite order Q affect it.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem taylorPastedExtension_uniform_jets
    (Q : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      |x-(l+2*h)| ≤ D → |x-(r-2*h)| ≤ D → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  pm_313 L hL hleft taylorPastedExtension_left_transition_bound Q R hR hright taylorPastedExtension_right_transition_bound
  let G : ℝ := (Q+1 : ℕ)*D^Q
  have hG : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hD) Q)
  let C := 1+G+L+R
  pm_1608
  pm_182 hGC G C
  pm_182 hLC L C
  pm_182 hRC R C
  refine ⟨C,hC,?_⟩
  intro f l r h x M hh hh₁ hgap hf hb hdistL hdistR n hn
  pm_6424
  pm_7385 haR
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ ha 0 (Nat.zero_le _))
  by_cases hx₀ : x < l+h
  · rw [(taylorPastedExtension_eventuallyEq_left_polynomial f Q hh hgap hx₀).iteratedDeriv_eq n]
    pm_5947 hdistL ha
  · have hx₀' : l+h ≤ x := le_of_not_gt hx₀
    by_cases hx₁ : x ≤ l+2*h
    pm_7313 hleft hx₀' hx₁ hLC
    · have hx₁' : l+2*h < x := lt_of_not_ge hx₁
      by_cases hx₂ : x < r-2*h
      · rw [(taylorPastedExtension_eventuallyEq_plateau f Q hh ⟨hx₁',hx₂⟩).iteratedDeriv_eq n]
        exact (hb x ⟨by linarith,by linarith⟩ n (by omega)).trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hM)
      · have hx₂' : r-2*h ≤ x := le_of_not_gt hx₂
        by_cases hx₃ : x ≤ r-h
        pm_7313 hright hx₂' hx₃ hRC
        · have hx₃' : r-h < x := lt_of_not_ge hx₃
          rw [(taylorPastedExtension_eventuallyEq_right_polynomial f Q hh hgap hx₃').iteratedDeriv_eq n]
          pm_5947 hdistR haR

end TaoTrudgianYang2025
