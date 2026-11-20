module
/-
Adapted from selected proofs in Scott McColm's ZeroCount.lean at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be; MIT.
No upstream zero-count definition or project module is imported.
-/
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.ZetaCounting
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Filter MeromorphicOn
open scoped Topology ArithmeticFunction.Moebius ComplexOrder

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density.ZetaGrowth

theorem finset_analyticOrderNatAt_le_finsum_divisor {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsCompact U) (hpre : IsPreconnected U)
    {c : ℂ} (hc : c ∈ U) (hcOrder : analyticOrderAt f c ≠ ⊤)
    (S : Finset ℂ) (hSU : ∀ u ∈ S, u ∈ U) :
    ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor f U u : ℤ) : ℝ) := by
  classical
  let d := divisor f U
  have hfin := d.finiteSupport hU
  rw [finsum_eq_sum_of_support_subset d (s := S ∪ hfin.toFinset) (by
    intro u hu
    exact Finset.mem_union_right _ (hfin.mem_toFinset.mpr hu))]
  exact_mod_cast calc
    (∑ u ∈ S, (analyticOrderNatAt f u : ℤ)) = ∑ u ∈ S, d u := by
      apply Finset.sum_congr rfl
      intro u hu
      change _ = divisor f U u
      rw [hf.divisor_apply (hSU u hu), ← Nat.cast_analyticOrderNatAt
        (hf.analyticOrderAt_ne_top_of_isPreconnected hpre hc (hSU u hu) hcOrder)]
      simp
    _ ≤ ∑ u ∈ S ∪ hfin.toFinset, d u :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => hf.divisor_nonneg u)

theorem zeta_jensen_sphere_bound (T t : ℝ) (hT : T ≥ 8)
    (ht : t ∈ Set.Icc (T - 1) (2 * T)) :
    ∀ z ∈ Metric.sphere (2 + I * (t + 1/2)) (7/4),
      ‖riemannZeta z‖ ≤ 100 * T ^ (3:ℝ) := by
  intro z hz
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  let c : ℂ := 2 + I * (t + 1/2)
  have hzc : ‖z - c‖ = 7 / 4 := by simpa [c] using hz
  have hreDiff : |z.re - 2| ≤ 7 / 4 := by
    calc
      |z.re - 2| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := abs_re_le_norm _
      _ = 7 / 4 := hzc
  have himDiff : |z.im - (t + 1/2)| ≤ 7 / 4 := by
    calc
      |z.im - (t + 1/2)| = |(z - c).im| := by simp [c]
      _ ≤ ‖z - c‖ := abs_im_le_norm _
      _ = 7 / 4 := hzc
  have hre : (1 / 4 : ℝ) ≤ z.re := by
    have := (abs_le.mp hreDiff).1
    linarith
  have himPos : 1 ≤ z.im := by
    have := (abs_le.mp himDiff).1
    linarith [ht.1]
  have him : 1 ≤ |z.im| := himPos.trans (le_abs_self z.im)
  have hcNorm : ‖c‖ ≤ t + 5/2 := by
    calc
      ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖I * ((t + 1/2 : ℝ) : ℂ)‖ := by
        simpa [c] using norm_add_le (2 : ℂ) (I * ((t + 1/2 : ℝ) : ℂ))
      _ = 2 + ‖((t + 1/2 : ℝ) : ℂ)‖ := by simp
      _ = 2 + |t + 1/2| := by rw [norm_real, Real.norm_eq_abs]
      _ = t + 5/2 := by
        rw [abs_of_nonneg]
        · ring
        · linarith [ht.1]
  have hzNorm : ‖z‖ ≤ 3 * T := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = 7/4 + ‖c‖ := by rw [hzc]
      _ ≤ 7/4 + (t + 5/2) := by gcongr
      _ ≤ 3 * T := by linarith [ht.2]
  calc
    ‖riemannZeta z‖ ≤ 5 * ‖z‖ := norm_riemannZeta_le_five_mul_norm hre him
    _ ≤ 15 * T := by nlinarith [norm_nonneg z]
    _ ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT0 : 0 ≤ T := by linarith
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        15 * T ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring

theorem moebius_coeff_norm_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ ‖(1 : ℂ)‖ := by
  rw [Complex.norm_intCast, norm_one]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- On the line `Re(s) = 2`, the Möbius Dirichlet series has norm less than
`5 / 3`, by comparison with `ζ(2) = π² / 6`. -/
theorem moebius_LSeries_norm_lt_five_thirds (u : ℝ) :
    ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 + u * I)‖ <
      (5 / 3 : ℝ) := by
  let s : ℂ := 2 + u * I
  have hsRe : s.re = 2 := by simp [s]
  have hs : 1 < s.re := by rw [hsRe]; norm_num
  have hSumM : LSeriesSummable
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hSumTwo : LSeriesSummable 1 (2 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  rw [LSeries]
  calc
    ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
        ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hSumM.norm
    _ ≤ ∑' n, ‖LSeries.term 1 (2 : ℂ) n‖ := by
      apply hSumM.norm.tsum_le_tsum _ hSumTwo.norm
      intro n
      calc
        ‖LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
            ‖LSeries.term 1 s n‖ :=
          LSeries.norm_term_le s (moebius_coeff_norm_le_one n)
        _ = ‖LSeries.term 1 (2 : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsRe]
          norm_num
    _ = (LSeries 1 (2 : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hSumTwo]
      apply tsum_congr
      intro n
      have hn : (0 : ℂ) ≤ LSeries.term 1 (2 : ℝ) n :=
        LSeries.term_nonneg (by simp) 2
      have heq := congrArg Complex.re (Complex.norm_of_nonneg' hn)
      simpa using heq
    _ = Real.pi ^ 2 / 6 := by
      rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two]
      norm_cast
    _ < 5 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- Lower bound on the line `Re(s) = 2`, obtained from the absolutely
convergent Möbius inverse of the zeta Dirichlet series. -/
theorem euler_product_lower_bound_2 (t : ℝ) :
    (0.6 : ℝ) ≤ ‖riemannZeta (2 + I * (t + 1 / 2))‖ := by
  let s : ℂ := 2 + I * (t + 1 / 2)
  have hsRe : s.re = 2 := by simp [s]
  have hs : 1 < s.re := by rw [hsRe]; norm_num
  have hprod :
      riemannZeta s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have hnormprod := congrArg norm hprod
  rw [norm_mul, norm_one] at hnormprod
  have hM : ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤ 5 / 3 := by
    have h := moebius_LSeries_norm_lt_five_thirds (t + 1 / 2)
    simpa [s, mul_comm] using h.le
  have hone : (1 : ℝ) ≤ ‖riemannZeta s‖ * (5 / 3) := by
    calc
      (1 : ℝ) = ‖riemannZeta s‖ *
          ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ := hnormprod.symm
      _ ≤ ‖riemannZeta s‖ * (5 / 3) := by gcongr
  change (0.6 : ℝ) ≤ ‖riemannZeta s‖
  nlinarith [norm_nonneg (riemannZeta s)]


private theorem jensen_height_majorant {T : ℝ} (hT : 8 ≤ T) : 1 ≤ 100 * T ^ (3 : ℝ) := by
  have h := Real.one_le_rpow (by linarith : 1 ≤ T) (by norm_num : (0 : ℝ) ≤ 3)
  linarith

/-- The logarithmic numerator in the unit-bin Jensen bound is independent of the disk. -/
theorem jensen_log_height_bound {T : ℝ} (hT : 0 < T) (hlog : 2 ≤ Real.log T) :
    Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) ≤ 100*Real.log T := by
  rw [show 100*T^(3 : ℝ)/(0.6 : ℝ) = (500/3)*T^(3 : ℝ) by ring,
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT]
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 500/3)]

theorem jensen_unit_bound_nonneg {T r : ℝ} (hT : 8 ≤ T) (hr : 0 < r) (hrR : r < 7/4) :
    0 ≤ Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) / Real.log ((7/4)/r) :=
  div_nonneg (Real.log_nonneg ((le_div_iff₀ (by norm_num)).2 (by
    linarith [jensen_height_majorant hT])))
    (Real.log_nonneg ((le_div_iff₀ hr).2 (by linarith)))

/-- Jensen's inequality for any finite sample inside one height bin. The radius
is chosen from the left edge of the strip and the bin's half-height. -/
theorem finset_unit_bin_le_jensen (S : Finset ℂ) {T a z r : ℝ}
    (hT : 8 ≤ T) (hr : 0 < r) (hrR : r < 7/4)
    (hrad : (2-a)^2+(1/2)^2 ≤ r^2)
    (hS : ∀ ρ ∈ S, a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ T ≤ ρ.im ∧ ρ.im ≤ 2*T ∧ z ≤ ρ.im ∧ ρ.im < z+1) :
    ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) / Real.log ((7/4)/r) := by
  obtain rfl | ⟨ρ, hρ⟩ := S.eq_empty_or_nonempty
  · simpa using jensen_unit_bound_nonneg hT hr hrR
  · obtain ⟨_, _, h₁, h₂, h₃, h₄⟩ := hS ρ hρ
    have hz : z ∈ Set.Icc (T-1) (2*T) := ⟨by linarith, by linarith⟩
    let c : ℂ := 2 + I * ((z : ℂ) + 1/2)
    have hA : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (7/4)) := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hd := (abs_im_le_norm (w-c)).trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)
      have hi := (abs_le.mp hd).1
      simp [c] at hi
      intro he
      change w = 1 at he
      subst w
      norm_num at hi
      linarith [hz.1]
    have hc := euler_product_lower_bound_2 z
    have hcn : riemannZeta c ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 0.6) hc)
    have hsub : ∀ w ∈ S, w ∈ Metric.closedBall c r := by
      intro w hw
      obtain ⟨ha, hb, _, _, hd, he⟩ := hS w hw
      have hx : |(w-c).re| ≤ 2-a := by
        rw [abs_le]; simp [c]; constructor <;> linarith
      have hy : |(w-c).im| ≤ 1/2 := by
        rw [abs_le]; simp [c]; constructor <;> linarith
      rw [Metric.mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) hr.le,
        sq, Complex.norm_mul_self_eq_normSq, normSq_apply]
      linarith [sq_le_sq.mpr (hx.trans (le_abs_self _)), sq_le_sq.mpr (hy.trans (le_abs_self _))]
    have hb := finset_analyticOrderNatAt_le_finsum_divisor
      (hA.mono (Metric.closedBall_subset_closedBall hrR.le)) (isCompact_closedBall c r)
      (convex_closedBall c r).isPreconnected (Metric.mem_closedBall_self hr.le)
      ((analyticOrderAt_eq_zero.mpr (Or.inr hcn)).trans_ne (by simp)) S hsub
    have hJ : ((∑ᶠ u, divisor riemannZeta (Metric.closedBall c r) u : ℤ) : ℝ) ≤
        Real.log ((100*T^(3 : ℝ))/‖riemannZeta c‖) / Real.log ((7/4)/r) := by
      have h :=
        (show AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c |(7/4 : ℝ)|) by
          simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using hA).sum_divisor_le (r := r) (R := 7/4)
          (by rwa [abs_of_pos hr]) (by simpa [abs_of_pos hr, abs_of_pos (by norm_num : (0 : ℝ) < 7/4)])
          (jensen_height_majorant hT) hcn (by
            simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using zeta_jensen_sphere_bound T z hT hz)
      rwa [abs_of_pos hr] at h
    refine hb.trans (hJ.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos ((one_lt_div hr).2 hrR)).le))
    have hTp : 0 < T := by linarith
    exact Real.log_le_log (div_pos (by positivity) (norm_pos_iff.mpr hcn))
      (div_le_div_of_nonneg_left (by positivity) (by norm_num) hc)

end MathCollab.Density.ZetaGrowth
