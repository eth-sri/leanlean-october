module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import GuthMaynard.NativeSource.GuthMaynard.MeanValueCS
public import GuthMaynard.NativeSource.GuthMaynard.MeanValue
public import GuthMaynard.NativeSource.GuthMaynard.Separated
public import MathCollab.Density.Stronger.Fourth.MeanValueCore
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set
open scoped Interval ComplexConjugate

namespace GuthMaynard.NativeMoment

export MathCollab.Density.Stronger.Fourth (integral_conj_dirichlet_term_mul_dirichlet_term integral_conj_dirichletTime_mul_dirichletTime abs_inv_log_sub_sub_div_le_one integral_norm_sq_dirichletTime_le integral_sawtooth_conj_fourier_mul_fourier integral_conj_fourier_term_mul_fourier_term natMainQuad_norm_le integral_sawtooth_conj_trigPoly_mul_trigPoly integral_conj_trigPoly_mul_trigPoly norm_sawtooth_conj_trigPoly_mul_trigPoly_le natScaledCoeff_l2_le logHilbertQuad_norm_le integral_cexp_int nat_hilbertForm_norm_le natMainQuad_eq_scaled_hilbert ofReal_integral_norm_sq_dirichletTime integral_sawtooth_cexp_all norm_complex_log_kernel_error_le_one integral_norm_sq_trigPoly logKernelErrorQuad norm_endpointTwist natMainQuad logHilbertQuad_eq_main_add_error logHilbertQuad continuous_trigPoly hilbertForm dirichletTime trigPoly endpointTwist natScaledCoeff)

export MathCollab.Density.Stronger.Fourth (integral_sawtooth_cexp)

theorem hilbertForm_norm_le (s : Finset ℤ) (a b : ℤ → ℂ) :
    ‖hilbertForm s a b‖ ≤
      Real.pi * ((∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖b n‖ ^ 2) := by pf_31 norm.fun_pow

lemma logKernelErrorQuad_norm_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    ‖logKernelErrorQuad N a‖ ≤
      (N : ℝ) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by pf_56 GuthMaynard.NativeMoment.sum_sq_le_card_mul_sum_sq

lemma local_sample_le_energy (g : ℝ → ℂ) (t : ℝ)
    (hg : Differentiable ℝ g) (hgd : Continuous (deriv g)) :
    ‖g t‖ ^ 2 ≤ ∫ x : ℝ in t..t + 1, 2 * ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2 := by
  pm_8710 h g
  let q : ℝ → ℝ := fun x => ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2
  have hhCont : Continuous h := hg.continuous.norm.fun_pow 2
  have hqCont : Continuous q := hg.continuous.norm.fun_pow 2 |>.add (hgd.norm.fun_pow 2)
  have hderivBound : ∀ y : ℝ, ‖deriv h y‖ ≤ q y := by
    intro y
    have hy := (hg y).hasDerivAt.norm_sq
    have hderiv := hy.deriv
    rw [hderiv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hinner : |inner ℝ (g y) (deriv g y)| ≤ ‖g y‖ * ‖deriv g y‖ :=
      abs_real_inner_le_norm _ _
    dsimp [q]
    calc
      2 * |inner ℝ (g y) (deriv g y)| ≤ 2 * (‖g y‖ * ‖deriv g y‖) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ ‖g y‖ ^ 2 + ‖deriv g y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖g y‖ - ‖deriv g y‖)]
  have hpoint : ∀ x ∈ Set.Icc t (t + 1), h t ≤ h x + ∫ y : ℝ in t..t + 1, q y := by
    intro x hx
    have htx : t ≤ x := hx.1
    have hdist : ‖h x - h t‖ ≤ ∫ y : ℝ in t..x, q y := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le htx
      · exact hhCont.continuousOn
      · intro y hy
        exact (hg y).hasDerivAt.norm_sq.differentiableAt.differentiableWithinAt
      · exact Filter.Eventually.of_forall fun y _hy => hderivBound y
      · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) t x
    have hmono : (∫ y : ℝ in t..x, q y) ≤ ∫ y : ℝ in t..t + 1, q y := by
      apply intervalIntegral.integral_mono_interval le_rfl htx hx.2
      · exact Filter.Eventually.of_forall fun y => by
          change 0 ≤ q y
          dsimp [q]
          positivity
      · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
    have hbasic : h t ≤ h x + ‖h x - h t‖ := by
      rw [Real.norm_eq_abs]
      linarith [neg_le_abs (h x - h t)]
    exact hbasic.trans (by
      simpa [add_comm] using add_le_add_left (hdist.trans hmono) (h x))
  let Q : ℝ := ∫ y : ℝ in t..t + 1, q y
  have hfInt : IntervalIntegrable (fun _ : ℝ => h t) MeasureTheory.volume t (t + 1) :=
    continuous_const.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
  have hgInt : IntervalIntegrable (fun x => h x + Q) MeasureTheory.volume t (t + 1) :=
    (hhCont.add continuous_const).intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
  have hpointQ : ∀ x ∈ Set.Icc t (t + 1), h t ≤ h x + Q := by
    simpa [Q] using hpoint
  have hmonoInt := intervalIntegral.integral_mono_on (show t ≤ t + 1 by linarith)
    hfInt hgInt hpointQ
  dsimp [h] at hmonoInt ⊢
  rw [intervalIntegral.integral_const] at hmonoInt
  norm_num at hmonoInt
  dsimp [Q, q] at hmonoInt
  refine hmonoInt.trans_eq ?_
  rw [intervalIntegral.integral_add
    (f := fun x => ‖g x‖ ^ 2)
    (g := fun _ => ∫ y : ℝ in t..t + 1, ‖g y‖ ^ 2 + ‖deriv g y‖ ^ 2)
    (hg.continuous.norm.fun_pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))]
  rw [intervalIntegral.integral_const]
  norm_num
  rw [← intervalIntegral.integral_add
    (f := fun x => ‖g x‖ ^ 2)
    (g := fun x => ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2)
    (hg.continuous.norm.fun_pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))
    ((hg.continuous.norm.fun_pow 2).add (hgd.norm.fun_pow 2) |>.intervalIntegrable
      (μ := MeasureTheory.volume) t (t + 1))]
  congr 1
  funext x
  ring

lemma sum_local_intervalIntegrals_le (T : ℝ) (W : Finset ℝ) (q : ℝ → ℝ)
    (hSep : GuthMaynard.NativeMoment.IsSeparated 1 W)
    (hBase : GuthMaynard.NativeMoment.InBaseInterval T W)
    (hT : 0 ≤ T) (hqCont : Continuous q) (hqNonneg : ∀ x, 0 ≤ q x) :
    (∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x) ≤ ∫ x : ℝ in 0..T + 1, q x := by
  let A : ℝ → Set ℝ := fun t => Set.Ioc t (t + 1)
  have hPair : Set.Pairwise (↑W : Set ℝ) (Function.onFun Disjoint A) := by
    intro x hx y hy hxy
    change Disjoint (A x) (A y)
    rw [Set.disjoint_left]
    intro z hzx hzy
    have hdist := hSep x hx y hy hxy
    rw [Real.dist_eq] at hdist
    have hxData : x < z ∧ z ≤ x + 1 := hzx
    have hyData : y < z ∧ z ≤ y + 1 := hzy
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · have : 1 ≤ y - x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxylt.le)] at hdist
        simpa only [neg_sub] using hdist
      linarith
    · have : 1 ≤ x - y := by
        rw [abs_of_nonneg (sub_nonneg.mpr hyxlt.le)] at hdist
        exact hdist
      linarith
  have hUnionSubset : (⋃ t ∈ W, A t) ⊆ Set.Ioc 0 (T + 1) := by
    intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨t, hz⟩ := hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨htW, hzt⟩ := hz
    have htBase := hBase t htW
    exact ⟨lt_of_le_of_lt htBase.1 hzt.1, by linarith [hzt.2, htBase.2]⟩
  have hUnionEq :
      (∫ x in ⋃ t ∈ W, A t, q x) = ∑ t ∈ W, ∫ x in A t, q x := by
    apply MeasureTheory.integral_biUnion_finset W
    · intro t ht
      exact measurableSet_Ioc
    · exact hPair
    · intro t ht
      exact (hqCont.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)).1
  have hMono : (∫ x in ⋃ t ∈ W, A t, q x) ≤ ∫ x in Set.Ioc 0 (T + 1), q x := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) 0 (T + 1) |>.1
    · exact Filter.Eventually.of_forall fun x => hqNonneg x
    · exact hUnionSubset.eventuallyLE
  rw [hUnionEq] at hMono
  have hLocal : ∀ t ∈ W, (∫ x : ℝ in t..t + 1, q x) = ∫ x in A t, q x := by
    intro t ht
    rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + 1)]
  calc
    (∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x) = ∑ t ∈ W, ∫ x in A t, q x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hLocal t ht
    _ ≤ ∫ x in Set.Ioc 0 (T + 1), q x := hMono
    _ = ∫ x : ℝ in 0..T + 1, q x := by
      rw [intervalIntegral.integral_of_le (by linarith)]

/-- The `centeredDirichletTime` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    a n * Complex.exp
      (Complex.I * (t : ℂ) * ((Real.log N - Real.log n : ℝ) : ℂ))

/-- The `centeredDerivCoeff` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def centeredDerivCoeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * (Complex.I * ((Real.log N - Real.log n : ℝ) : ℂ))

section
variable (N : ℕ) (a : ℕ → ℂ)
include N a
lemma centeredDirichletTime_eq (t : ℝ) :
    centeredDirichletTime N a t =
      Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) * dirichletTime N a t := by
  pm_424 centeredDirichletTime dirichletTime Finset.mul_sum Finset.sum_congr
  intro n hn
  rw [show Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
      (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
    a n * (Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
      Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) by ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

lemma norm_centeredDirichletTime (t : ℝ) :
    ‖centeredDirichletTime N a t‖ = ‖dirichletTime N a t‖ := by
  rw [centeredDirichletTime_eq, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (Real.log N : ℂ)).re = 0 := by
    pm_188 Complex.mul_re Complex.I_re Complex.I_im Complex.ofReal_re Complex.ofReal_im
    ring_nf
  rw [hre, Real.exp_zero, one_mul]

lemma hasDerivAt_centeredDirichletTime (t : ℝ) :
    HasDerivAt (centeredDirichletTime N a)
      (centeredDirichletTime N (centeredDerivCoeff N a) t) t := by
  unfold centeredDirichletTime
  apply HasDerivAt.fun_sum
  intro n hn
  pm_7660 N n
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
      (Complex.exp (c * (t : ℂ)) * c) t := by
    convert (Complex.hasDerivAt_exp (c * (t : ℂ))).comp t
      (((hasDerivAt_id t).ofReal_comp).const_mul c) using 1
    all_goals simp [Function.comp_def]
  convert hexp.const_mul (a n) using 1
  · funext y
    congr 2
    dsimp [c]
    ring
  · dsimp [centeredDerivCoeff, c]
    ring_nf

lemma differentiable_centeredDirichletTime :
    Differentiable ℝ (centeredDirichletTime N a) := by
  intro t
  exact (hasDerivAt_centeredDirichletTime N a t).differentiableAt

lemma deriv_centeredDirichletTime (t : ℝ) :
    deriv (centeredDirichletTime N a) t =
      centeredDirichletTime N (centeredDerivCoeff N a) t :=
  (hasDerivAt_centeredDirichletTime N a t).deriv

lemma continuous_deriv_centeredDirichletTime :
    Continuous (deriv (centeredDirichletTime N a)) := by
  rw [show deriv (centeredDirichletTime N a) =
      centeredDirichletTime N (centeredDerivCoeff N a) by
    funext t
    exact deriv_centeredDirichletTime N a t]
  exact differentiable_centeredDirichletTime N (centeredDerivCoeff N a) |>.continuous
end

lemma abs_log_ratio_le_one (N n : ℕ) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2 * N)) :
    |Real.log N - Real.log n| ≤ 1 := by
  pm_74 hNR N hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast
    (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
  pm_7142 hNn
  pm_6650 hn2N
  have hlogNn : Real.log N ≤ Real.log n := Real.log_le_log hNR hNn
  have hlogn2N : Real.log n ≤ Real.log (2 * N) := Real.log_le_log hnR hn2N
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [abs_of_nonpos (sub_nonpos.mpr hlogNn)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hN.ne') ] at hlogn2N
  linarith

lemma centeredDerivCoeff_l2_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2 * N), ‖centeredDerivCoeff N a n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  rw [centeredDerivCoeff, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hlog := abs_log_ratio_le_one N n hN hn
  have hnonneg : 0 ≤ |Real.log N - Real.log n| := abs_nonneg _
  have ha : 0 ≤ ‖a n‖ := norm_nonneg _
  have hmul : ‖a n‖ * |Real.log N - Real.log n| ≤ ‖a n‖ :=
    mul_le_of_le_one_right ha hlog
  nlinarith [sq_nonneg (‖a n‖ - ‖a n‖ * |Real.log N - Real.log n|)]

lemma nat_cpow_neg_mul_I_eq (n : ℕ) (t : ℝ) (hn : 0 < n) :
    (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  congr 1
  ring

theorem montgomery_mean_value_estimate (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 1 ≤ T)
    (hSep : GuthMaynard.NativeMoment.IsSeparated 1 W)
    (hBase : GuthMaynard.NativeMoment.InBaseInterval T W) :
    (∑ t ∈ W, ‖∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2) ≤
      (3 * (2 + 2 * (5 * Real.pi + 1))) * (T + (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let g : ℝ → ℂ := centeredDirichletTime N a
  let b : ℕ → ℂ := centeredDerivCoeff N a
  let q : ℝ → ℝ := fun x => 2 * ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2
  pm_1590
  let K : ℝ := 2 * (5 * Real.pi + 1)
  let U : ℝ := T + 1
  pm_165 hS S
  pm_165 hK K
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hphase : ∀ t ∈ W,
      (∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        dirichletTime N a t := by
    intro t ht
    apply Finset.sum_congr rfl
    intro n hn
    rw [nat_cpow_neg_mul_I_eq n t
      (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)]
  have hgDiff : Differentiable ℝ g := differentiable_centeredDirichletTime N a
  have hgdCont : Continuous (deriv g) := continuous_deriv_centeredDirichletTime N a
  have hqCont : Continuous q := by
    dsimp [q]
    exact (hgDiff.continuous.norm.fun_pow 2).const_mul 2 |>.add (hgdCont.norm.fun_pow 2)
  have hqNonneg : ∀ x, 0 ≤ q x := by
    intro x
    dsimp [q]
    positivity
  have hLocal : ∀ t ∈ W, ‖g t‖ ^ 2 ≤ ∫ x : ℝ in t..t + 1, q x := by
    intro t ht
    exact local_sample_le_energy g t hgDiff hgdCont
  have hDisjoint := sum_local_intervalIntegrals_le T W q hSep hBase
    (by linarith : 0 ≤ T) hqCont hqNonneg
  have hMain : (∫ x : ℝ in 0..U, ‖g x‖ ^ 2) ≤ (U + K * (N : ℝ)) * S := by
    dsimp [g, U, K, S]
    simpa only [norm_centeredDirichletTime] using
      integral_norm_sq_dirichletTime_le N (T + 1) a hN (by linarith)
  have hbL2 : (∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤ S := by
    exact centeredDerivCoeff_l2_le N a hN
  have hDerivRaw :
      (∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2) ≤
        (U + K * (N : ℝ)) * ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 := by
    dsimp [g, b, U, K]
    simp_rw [deriv_centeredDirichletTime, norm_centeredDirichletTime]
    exact integral_norm_sq_dirichletTime_le N (T + 1) (centeredDerivCoeff N a)
      hN (by linarith)
  have hFactor : 0 ≤ U + K * (N : ℝ) := by positivity
  have hDeriv : (∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2) ≤
      (U + K * (N : ℝ)) * S :=
    hDerivRaw.trans (mul_le_mul_of_nonneg_left hbL2 hFactor)
  have hGlobal : (∫ x : ℝ in 0..U, q x) ≤ 3 * (U + K * (N : ℝ)) * S := by
    dsimp [q]
    rw [intervalIntegral.integral_add
      ((hgDiff.continuous.norm.fun_pow 2).const_mul 2 |>.intervalIntegrable
        (μ := MeasureTheory.volume) 0 U)
      (hgdCont.norm.fun_pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) 0 U)]
    rw [intervalIntegral.integral_const_mul]
    calc
      2 * (∫ x : ℝ in 0..U, ‖g x‖ ^ 2) +
          ∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2 ≤
          2 * ((U + K * (N : ℝ)) * S) + (U + K * (N : ℝ)) * S := by
        exact add_le_add (mul_le_mul_of_nonneg_left hMain (by norm_num)) hDeriv
      _ = 3 * (U + K * (N : ℝ)) * S := by ring
  have hScale : U + K * (N : ℝ) ≤ (2 + K) * (T + (N : ℝ)) := by
    pm_74 hNR N hN
    dsimp [U]
    nlinarith
  calc
    (∑ t ∈ W, ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2) =
        ∑ t ∈ W, ‖g t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hphase t ht]
          dsimp [g]
          rw [norm_centeredDirichletTime]
    _ ≤ ∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x := by
      exact Finset.sum_le_sum hLocal
    _ ≤ ∫ x : ℝ in 0..T + 1, q x := hDisjoint
    _ ≤ 3 * (U + K * (N : ℝ)) * S := by simpa [U] using hGlobal
    _ ≤ 3 * ((2 + K) * (T + (N : ℝ))) * S := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScale (by norm_num)) hS
    _ = (3 * (2 + 2 * (5 * Real.pi + 1))) * (T + (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
      dsimp [K, S]
      ring

theorem montgomery_mean_value_native :
    GuthMaynard.NativeMoment.MontgomeryMeanValue := by
  refine ⟨3 * (2 + 2 * (5 * Real.pi + 1)), by positivity, ?_⟩
  intro N T W a hN hT hSep hBase
  exact montgomery_mean_value_estimate N T W a hN hT hSep hBase

end GuthMaynard.NativeMoment
