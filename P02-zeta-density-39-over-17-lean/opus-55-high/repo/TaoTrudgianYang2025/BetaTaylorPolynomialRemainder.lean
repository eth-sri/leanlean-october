module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaTaylorPolynomialJets
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Uniform local finite Taylor remainders

The polynomial uses the ordinary derivatives at an interior anchor.
Taylor's theorem on the genuine segment gives a bound involving only
the original highest derivative on that segment, for either orientation.
-/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem taylorWithinEval_uIcc_eq_finiteTaylorPolynomial
    {f : ℝ → ℝ} {a x : ℝ} (hax : a ≠ x)
    (hf : ContDiffAt ℝ ∞ f a) (n : ℕ) :
    taylorWithinEval f n (uIcc a x) a x = finiteTaylorPolynomial f n a x := by
  have hlt : min a x < max a x := by
    rcases lt_or_gt_of_ne hax with h | h
    grind
    grind
  have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_Icc hlt
  pm_8037
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv hu
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)) left_mem_uIcc,
    iteratedDerivWithin_univ]

theorem abs_finiteTaylorPolynomial_remainder_le
    {f : ℝ → ℝ} {a x M : ℝ} (n : ℕ)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (n+1) f y| ≤ M) :
    |f x-finiteTaylorPolynomial f n a x| ≤
      M*|x-a|^(n+1)/(n+1).factorial := by
  pm_1618
  · have hn : ((n+1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
    obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      (fun z hz => ((hf z hz).of_le hn).contDiffWithinAt)
    rw [taylorWithinEval_uIcc_eq_finiteTaylorPolynomial hax (hf a left_mem_uIcc) n] at he
    pm_1617

theorem iteratedDeriv_real_comp_order (i j : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i+j) f := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

theorem abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le
    {f : ℝ → ℝ} {a x M : ℝ} {j Q : ℕ} (hj : j ≤ Q)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) :
    |iteratedDeriv j (fun y => f y-finiteTaylorPolynomial f Q a y) x| ≤
      M*|x-a|^(Q+1-j) := by
  pm_1620
  have hN : (j : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [iteratedDeriv_fun_sub ((hf x right_mem_uIcc).of_le hN)
    ((finiteTaylorPolynomial_contDiff f Q a).contDiffAt.of_le hN),
    iteratedDeriv_finiteTaylorPolynomial f a hj]
  have h := abs_finiteTaylorPolynomial_remainder_le (f := iteratedDeriv j f)
    (a := a) (x := x) (M := M) (Q-j)
    (fun y hy => contDiffAt_iteratedDeriv_infty (hf y hy) j) ?_
  pm_1619

end TaoTrudgianYang2025
