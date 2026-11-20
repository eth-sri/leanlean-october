module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import RequestProject.PlanarNotation

/-!
# An actual smooth Fourier collar

The coefficient `a n` is the ordinary Taylor coefficient, hence the
averaged circle Fourier coefficient when that identification is proved.
No orthonormal Fourier normalization or square-root period is inserted.

The genuine cutoff is one on the negative half-line and zero past one.
The nth monomial is cut off at `n * (normSq z - 1) = 1`. On this support
`norm z ^ n ≤ exp (1/2)`. The real kth derivatives have a true uniform
bound `B k * n ^ k`, obtained from scalar restriction, finite compact
derivative bounds, and Mathlib's actual product/composition estimates.
Weighted absolute summability of the Taylor coefficients then proves
global real C∞ smoothness of the constructed series.

The final matching lemma consumes a genuine Taylor-series identity,
not an assumed extension or assumed smoothness of an infinite sum.
Deriving rapid decay and the Taylor identity from the eventual smooth
circle trace remains a separate boundary-regularity/Fourier step.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology

section

variable (N : ℕ∞) (a : ℕ → ℂ) (n k : ℕ) (z : ℂ)

/-- The actual transition, with precisely the required two constant sides. -/
def fourierCollarCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

theorem fourierCollarCutoff_one {t : ℝ} (ht : t ≤ 0) : fourierCollarCutoff t = 1 := by
  simp [fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos ht]

theorem fourierCollarCutoff_zero {t : ℝ} (ht : 1 ≤ t) : fourierCollarCutoff t = 0 := by
  simp [fourierCollarCutoff, Real.smoothTransition.one_of_one_le ht]

theorem fourierCollarCutoff_contDiff : ContDiff ℝ N fourierCollarCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

/-- Each derivative is truly bounded globally: outside the compact
transition interval the function is locally constant. -/
theorem fourierCollarCutoff_exists_derivative_bound (i : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv' (fourierCollarCutoff_contDiff i)).continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc 0 1
  · simp [*]
  · rcases lt_or_ge t 0 with ht0 | ht0
    · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
        filter_upwards [eventually_lt_nhds ht0] with s hs
        exact fourierCollarCutoff_one hs.le
      
      rw [((heq.iteratedFDeriv ℝ i).eq_of_nhds)]
      cases i with
      | zero => aesop
      | succ i =>
          simp [iteratedFDeriv_succ_const]
    · have ht1  := lt_of_not_ge (fun h => ht ⟨ht0, h⟩)
      have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
        filter_upwards [eventually_gt_nhds ht1] with s hs
        exact fourierCollarCutoff_zero hs.le
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      simp [hd]

/-- A finite family of the genuine global derivative bounds. -/
theorem fourierCollarCutoff_exists_finite_derivative_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ C := by
  choose B hB hbound using fourierCollarCutoff_exists_derivative_bound
  
  refine ⟨(max 1 (∑ i ∈ Finset.range (k + 1), B i)), le_max_left _ _, ?_⟩
  intro i hi t
  
  exact (hbound i t).trans ((Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))

include z in
def fourierCollarRadialDefect : ℝ := ‖z‖ ^ 2 - 1

theorem fourierCollarRadialDefect_contDiff : ContDiff ℝ N fourierCollarRadialDefect :=
  (contDiff_norm_sq ℂ).sub contDiff_const

/-- Compact bounds on the unscaled radial polynomial. These are actual
iterated derivatives, rather than an assumed Faà di Bruno estimate. -/
theorem fourierCollarRadialDefect_exists_finite_derivative_bound :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ k, ∀ z ∈ closedBall (0 : ℂ) 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ D := by
  have hbound (i : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ closedBall 0 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall 0 2).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv' (fourierCollarRadialDefect_contDiff i)).continuousOn
    exact ⟨max 1 B, le_max_left _ _, (by grind)⟩
  choose B hB hbound using hbound
  
  refine ⟨(max 1 (∑ i ∈ Finset.range (k + 1), B i)), le_max_left _ _, ?_⟩
  intro i hi z hz
  
  exact (hbound i z hz).trans ((Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))

include n z in
def fourierCollarScaledDefect : ℝ := (n : ℝ) * fourierCollarRadialDefect z

theorem fourierCollarScaledDefect_contDiff :
    ContDiff ℝ N (fourierCollarScaledDefect n) :=
  contDiff_const.mul (fourierCollarRadialDefect_contDiff N)

include n z in
def fourierCollarTerm : ℂ :=
  z ^ n * (fourierCollarCutoff (fourierCollarScaledDefect n z) : ℂ)

theorem fourierCollarTerm_contDiff : ContDiff ℝ N (fourierCollarTerm n) :=
  (contDiff_id.pow n).mul (Complex.ofRealCLM.contDiff.comp
    ((fourierCollarCutoff_contDiff N).comp (fourierCollarScaledDefect_contDiff N n)))

theorem fourierCollarTerm_eq_pow_on_closedDisk {z : ℂ} (hz : z ∈ closedDisk) :
    fourierCollarTerm n z = z ^ n := by
  have hr : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hq : fourierCollarScaledDefect n z ≤ 0 := by
    dsimp [fourierCollarScaledDefect, fourierCollarRadialDefect]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by simp [*])
  simp only [fourierCollarTerm, fourierCollarCutoff_one hq, Complex.ofReal_one, mul_one]

/-- The support radius remains in a fixed compact ball. -/
theorem fourierCollar_support_radius {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ 2 ≤ 1 + 1 / (n : ℝ) ∧ z ∈ closedBall (0 : ℂ) 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : ‖z‖ ^ 2 - 1 ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    change (‖z‖ ^ 2 - 1) * (n : ℝ) ≤ 1
    rw [mul_comm]
    exact hz
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
  refine ⟨by linarith, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  nlinarith

/-- The shrinking support compensates exactly for monomial growth.
This proves the uniform exponential constant instead of assuming it. -/
theorem fourierCollar_support_pow_le_exp_half {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    {z : ℂ} (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ m ≤ Real.exp (1 / 2 : ℝ) := by
  have hsupport := (fourierCollar_support_radius hn hz).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  
  rcases le_or_gt ‖z‖ 1 with hr | hr
  · exact (pow_le_one₀ (norm_nonneg z) hr).trans (by
    simp)
  · have hlog : (2 : ℝ) * Real.log ‖z‖ ≤ ‖z‖ ^ 2 - 1 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using
        Real.log_le_sub_one_of_pos (sq_pos_of_pos (lt_trans zero_lt_one hr))
    have hlog' : 2 * Real.log ‖z‖ ≤ 1 / (n : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlog' hn0.le
    have hcancel : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn0.ne']
    rw [hcancel] at hmul
    
    have hnpow : ‖z‖ ^ n ≤ Real.exp (1 / 2 : ℝ) := by
      have heq : ‖z‖ ^ n = Real.exp ((n : ℝ) * Real.log ‖z‖) := by
        rw [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr)]
      rw [heq]
      exact Real.exp_le_exp.mpr (by nlinarith)
    exact (pow_le_pow_right₀ hr.le hm).trans hnpow

/-- The exact real derivative norm of a holomorphic monomial. -/
theorem fourierCollar_pow_iteratedFDeriv_norm :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n) z‖ =
      (n.descFactorial k : ℝ) * ‖z‖ ^ (n - k) := by
  have hp : ContDiffAt ℂ k (fun w : ℂ => w ^ n) z := (contDiff_id.pow n).contDiffAt
  rw [← hp.restrictScalars_iteratedFDeriv ]
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

theorem fourierCollar_pow_iteratedFDeriv_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n) z‖ ≤ (n : ℝ) ^ k * Real.exp (1 / 2 : ℝ) := by
  rw [fourierCollar_pow_iteratedFDeriv_norm]
  
  refine mul_le_mul ?_ (fourierCollar_support_pow_le_exp_half hn (Nat.sub_le _ _) hz)
    (by positivity) (by positivity)
  exact_mod_cast Nat.descFactorial_le_pow n k

/-- True uniform kth-order bounds for the individual collar summands. -/
theorem fourierCollarTerm_exists_iteratedFDeriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ,
      ‖iteratedFDeriv ℝ k (fourierCollarTerm n) z‖ ≤ B * (n : ℝ) ^ k := by
  obtain ⟨C, hC, hχ⟩ := fourierCollarCutoff_exists_finite_derivative_bound k
  obtain ⟨D, hD, hq⟩ := fourierCollarRadialDefect_exists_finite_derivative_bound k
  let B := ∑ i ∈ Finset.range (k + 1),
    (k.choose i) * Real.exp (1 / 2 : ℝ) * (k - i).factorial * C * D ^ (k - i)
  have hBdef : B = ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i) := rfl
  have hB : 0 ≤ B := by
    exact (by positivity)
  refine ⟨B, hB, ?_⟩
  intro n hn z
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hz : fourierCollarScaledDefect n z ≤ 1
  · 
    have hscaled (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ ≤ (n * D) ^ i := by
      have hscale : ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ =
          (n : ℝ) * ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ := by
        change ‖iteratedFDeriv ℝ i (fun w => (n : ℝ) • fourierCollarRadialDefect w) z‖ = _
        rw [iteratedFDeriv_const_smul_apply'
          (fourierCollarRadialDefect_contDiff (i : ℕ∞)).contDiffAt, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hn0.le]
      rw [hscale]
      have hND : 1 ≤ (n : ℝ) * D := by
        simpa only [one_mul] using mul_le_mul hn1 hD (by norm_num : (0 : ℝ) ≤ 1) hn0.le
      exact (mul_le_mul_of_nonneg_left (hq i hi z ((fourierCollar_support_radius hn hz).2)) hn0.le).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hND hi1)
    have hcut (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j
          (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          j.factorial * C * (n * D) ^ j := by
      have hc := norm_iteratedFDeriv_comp_le (fourierCollarCutoff_contDiff j)
        (fourierCollarScaledDefect_contDiff j n) le_rfl z
        (fun i hi => hχ i (hi.trans hj) _) (fun i hi1 hi => hscaled i hi1 (hi.trans hj))
      have hnrm := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := z)
        (((fourierCollarCutoff_contDiff j).comp
          (fourierCollarScaledDefect_contDiff j n)).contDiffAt) le_rfl
      exact hnrm.le.trans hc
    have hprod := norm_iteratedFDeriv_mul_le
      (show ContDiff ℝ (k : ℕ∞) (fun w : ℂ => w ^ n) from contDiff_id.pow n)
      (Complex.ofRealCLM.contDiff.comp ((fourierCollarCutoff_contDiff k).comp
        (fourierCollarScaledDefect_contDiff k n))) z le_rfl
    
    apply hprod.trans
    rw [hBdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    
    
    
    have hcut' := hcut (k - i) (Nat.sub_le _ _)
    have hmul := mul_le_mul (fourierCollar_pow_iteratedFDeriv_le hn i hz) hcut' (norm_nonneg _) (by positivity)
    have hchosen := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ k.choose i from Nat.cast_nonneg _)
    calc
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : ℂ => w ^ n) z‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          (k.choose i) * (n ^ i * Real.exp (1 / 2 : ℝ)) *
            ((k - i).factorial * C * (n * D) ^ (k - i)) := by
        simpa only [mul_assoc] using hchosen
      _ = ((k.choose i) * Real.exp (1 / 2 : ℝ) * (k - i).factorial * C * D ^ (k - i)) *
          (n ^ i * n ^ (k - i)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  · 
    have heq : fourierCollarTerm n =ᶠ[𝓝 z] (fun _ : ℂ => 0) := by
      have hopen  :=
        (isOpen_lt continuous_const (fourierCollarScaledDefect_contDiff 0 n).continuous).mem_nhds (lt_of_not_ge hz)
      filter_upwards [hopen] with w hw
      simp [fourierCollarTerm, fourierCollarCutoff_zero hw.le, Complex.ofReal_zero, mul_zero]
    
    rw [((heq.iteratedFDeriv ℝ k).eq_of_nhds)]
    simp
    exact mul_nonneg hB (pow_nonneg hn0.le _)

include a in
/-- All polynomially weighted ordinary Taylor coefficients are absolutely
summable. This is an intermediate Fourier regularity input, not a collar. -/
def HasRapidFourierDecay : Prop :=
  ∀ k : ℕ, Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k)

include a z in
def fourierCollarExtension : ℂ :=
  a 0 + ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z

/-- Smoothness of the constructed series follows from actual uniform
derivative majorants, rather than a smooth-series premise. -/
theorem fourierCollarExtension_contDiff {a : ℕ → ℂ} (ha : HasRapidFourierDecay a) :
    ContDiff ℝ ∞ (fourierCollarExtension a) := by
  choose B hB hbound using fourierCollarTerm_exists_iteratedFDeriv_bound
  
  apply contDiff_const.add
  apply contDiff_tsum 
  · intro n
    exact (fourierCollarTerm_contDiff (⊤ : ℕ∞) (n + 1)).const_smul (a (n + 1))
  · intro k _
    exact (ha k).mul_left (B k)
  · intro k n z _
    rw [iteratedFDeriv_const_smul_apply'
      (fourierCollarTerm_contDiff (k : ℕ∞) (n + 1)).contDiffAt, norm_smul]
    calc
      _ ≤
          ‖a (n + 1)‖ * (B k * ((n + 1 : ℕ) : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hbound k (n + 1) (by omega) z) (norm_nonneg _)
      _ = _ := by ring

/-- Every summand agrees with its actual Taylor monomial on the
closed disk, including the boundary. The zeroth coefficient is separate. -/
theorem fourierCollarExtension_eq_taylor_on_closedDisk {z : ℂ}
    (hz : z ∈ closedDisk) :
    fourierCollarExtension a z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1) := by
  unfold fourierCollarExtension
  congr 1
  apply tsum_congr
  intro n
  rw [fourierCollarTerm_eq_pow_on_closedDisk (n + 1) hz]
  rfl

end

/-- A genuine smooth collar from genuine rapidly decaying Taylor data.
The input equality is a Taylor-series identity for F, never an assumed
extension or an assumed infinite-sum differentiability assertion. -/
theorem exists_smooth_fourier_collar_of_taylor {a : ℕ → ℂ} (ha : HasRapidFourierDecay a)
    {F : ℂ → ℂ} (hTaylor : ∀ z ∈ closedDisk,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧ EqOn G F closedDisk := by
  refine ⟨fourierCollarExtension a, fourierCollarExtension_contDiff ha, ?_⟩
  intro z hz
  rw [fourierCollarExtension_eq_taylor_on_closedDisk a hz, hTaylor z hz]

/-- Interior complex holomorphicity is inherited from the actual F.
Only real smoothness is asserted outside the disk. -/
theorem exists_smooth_holomorphic_fourier_collar_of_taylor {a : ℕ → ℂ}
    (ha : HasRapidFourierDecay a) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisk)
    (hTaylor : ∀ z ∈ closedDisk,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧
      EqOn G F closedDisk ∧ DifferentiableOn ℂ G unitDisk := by
  obtain ⟨G, hG, hGF⟩ := exists_smooth_fourier_collar_of_taylor ha hTaylor
  exact ⟨G, hG, hGF, hF.congr (fun z hz => hGF (ball_subset_closedBall hz))⟩

end PolyaNeumann
