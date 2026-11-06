module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaTaylorPastedExtension
public import TaoTrudgianYang2025.BetaTaylorPolynomialBudget
import WeylPort.Analytic.RealLaplace

public section

/-!
# Both closed transition bands of the actual pasted extension

Boundary points stay in the transition estimates. Each local formula
uses the genuine Taylor remainder, so no negative power of the width
appears in the final derivative bound.
-/


open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

set_option hygiene false in
macro "pc_407" x1:ident x2:ident x3:ident : tactic => `(tactic| (
  have ht : ContDiffAt ℝ ∞ ($x1:ident $x2:ident h) x :=
    (Real.smoothTransition.contDiff.comp (by fun_prop)).contDiffAt
  rw [($x3:ident f Q hh hlocal).iteratedDeriv_eq n,
    iteratedDeriv_fun_add (hp.of_le hN) ((ht.mul ((hf x hxI).sub hp)).of_le hN)]
  exact (abs_add_le _ _).trans ((add_le_add hpoly hrem).trans_eq (by ring))))
theorem taylorPastedExtension_left_transition_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      x ∈ Icc (l+h) (l+2*h) → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  pm_1623
  pm_6424
  pm_6211
  have hdist : |x-(l+2*h)| ≤ h := by
    pm_7734
  have hseg : uIcc (l+2*h) x ⊆ Ioo l r := by
    pm_5805
  have harg (y : ℝ) : (y-l)/h-1 = 1*y/h+(-l/h-1) := by ring
  have hrem : |iteratedDeriv n (fun y => taylorLeftTransition l h y*
      (f y-finiteTaylorPolynomial f Q (l+2*h) y)) x| ≤ B*M := by
    simpa only [taylorLeftTransition,harg] using
      htr f (l+2*h) x h 1 (-l/h-1) M hh hh₁ (by norm_num) hdist
        (fun y hy => hf y (hseg hy))
        (fun y hy => hb y (hseg hy) (Q+1) le_rfl) n hn
  have hpoly : |iteratedDeriv n (finiteTaylorPolynomial f Q (l+2*h)) x| ≤ (Q+1 : ℕ)*M := by
    pm_1624
  have hlocal : x < r-2*h := by linarith [hx.1,hx.2]
  pb_1292
  have hp : ContDiffAt ℝ ∞ (finiteTaylorPolynomial f Q (l+2*h)) x :=
    (finiteTaylorPolynomial_contDiff f Q (l+2*h)).contDiffAt
  pc_407 taylorLeftTransition l taylorPastedExtension_eventuallyEq_left_formula

theorem taylorPastedExtension_right_transition_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      x ∈ Icc (r-2*h) (r-h) → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  pm_1623
  pm_7385 ha
  pm_6211
  have hdist : |x-(r-2*h)| ≤ h := by
    pm_7734
  have hseg : uIcc (r-2*h) x ⊆ Ioo l r := by
    pm_5805
  have harg (y : ℝ) : (r-y)/h-1 = (-1)*y/h+(r/h-1) := by ring
  have hrem : |iteratedDeriv n (fun y => taylorRightTransition r h y*
      (f y-finiteTaylorPolynomial f Q (r-2*h) y)) x| ≤ B*M := by
    simpa only [taylorRightTransition,harg] using
      htr f (r-2*h) x h (-1) (r/h-1) M hh hh₁ (by norm_num) hdist
        (fun y hy => hf y (hseg hy))
        (fun y hy => hb y (hseg hy) (Q+1) le_rfl) n hn
  have hpoly : |iteratedDeriv n (finiteTaylorPolynomial f Q (r-2*h)) x| ≤ (Q+1 : ℕ)*M := by
    pm_1624
  have hlocal : l+2*h < x := by linarith [hx.1,hx.2]
  pb_1292
  have hp : ContDiffAt ℝ ∞ (finiteTaylorPolynomial f Q (r-2*h)) x :=
    (finiteTaylorPolynomial_contDiff f Q (r-2*h)).contDiffAt
  pc_407 taylorRightTransition r taylorPastedExtension_eventuallyEq_right_formula

end TaoTrudgianYang2025
