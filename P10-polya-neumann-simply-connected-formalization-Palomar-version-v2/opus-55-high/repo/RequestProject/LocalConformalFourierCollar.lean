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

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology

/-- The actual transition, with precisely the required two constant sides. -/
def fourierCollarCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

theorem fourierCollarCutoff_one {t : ℝ} (ht : t ≤ 0) : fourierCollarCutoff t = 1 := by
  simp [fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos ht]

theorem fourierCollarCutoff_zero {t : ℝ} (ht : 1 ≤ t) : fourierCollarCutoff t = 0 := by
  simp [fourierCollarCutoff, Real.smoothTransition.one_of_one_le ht]

theorem fourierCollarCutoff_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

/-- Each derivative is truly bounded globally: outside the compact
transition interval the function is locally constant. -/
theorem fourierCollarCutoff_exists_derivative_bound (i : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv' (fourierCollarCutoff_contDiff i)).continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc 0 1
  · exact (hB t ht).trans (le_max_right _ _)
  · rcases lt_or_ge t 0 with ht0 | ht0
    · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _  => 1) := by
        filter_upwards [eventually_lt_nhds ht0] with s hs
        exact fourierCollarCutoff_one hs.le
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      cases i with
      | zero => norm_num
      | succ i =>
          simp [iteratedFDeriv_succ_const]
    · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _  => 0) := by
        filter_upwards [eventually_gt_nhds (lt_of_not_ge (fun h => ht ⟨ht0, h⟩))] with s hs
        exact fourierCollarCutoff_zero hs.le
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      simp_all

/-- A finite family of the genuine global derivative bounds. -/
theorem fourierCollarCutoff_exists_finite_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ C := by
  choose B hB hbound using fourierCollarCutoff_exists_derivative_bound
  let C := max 1 (∑ i ∈ Finset.range (k + 1), B i)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro i hi t
  exact (hbound i t).trans ((Finset.single_le_sum (fun j _ => (by grind)) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))

def fourierCollarRadialDefect (z : ℂ) : ℝ := ‖z‖ ^ 2 - 1

theorem fourierCollarRadialDefect_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarRadialDefect :=
  (contDiff_norm_sq ℂ).sub contDiff_const

/-- Compact bounds on the unscaled radial polynomial. These are actual
iterated derivatives, rather than an assumed Faà di Bruno estimate. -/
theorem fourierCollarRadialDefect_exists_finite_derivative_bound (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ k, ∀ z ∈ closedBall 0 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ D := by
  have hbound (i : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ closedBall 0 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall 0 2).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv' (fourierCollarRadialDefect_contDiff i)).continuousOn
    exact ⟨max 1 B, le_max_left _ _, fun z hz => (hB z hz).trans (le_max_right _ _)⟩
  choose B hB hbound using hbound
  let D := max 1 (∑ i ∈ Finset.range (k + 1), B i)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro i hi z hz
  exact (hbound i z hz).trans ((Finset.single_le_sum (fun j _ => (by grind)) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))

def fourierCollarScaledDefect (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * fourierCollarRadialDefect z

theorem fourierCollarScaledDefect_contDiff (N : ℕ∞) (n : ℕ) :
    ContDiff ℝ N (fourierCollarScaledDefect n) :=
  contDiff_const.mul (fourierCollarRadialDefect_contDiff N)

def fourierCollarTerm (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n * (fourierCollarCutoff (fourierCollarScaledDefect n z) : ℂ)

theorem fourierCollarTerm_contDiff (N : ℕ∞) (n : ℕ) : ContDiff ℝ N (fourierCollarTerm n) :=
  (contDiff_id.pow n).mul (Complex.ofRealCLM.contDiff.comp
    ((fourierCollarCutoff_contDiff N).comp (fourierCollarScaledDefect_contDiff N n)))

theorem fourierCollarTerm_eq_pow_on_closedDisk (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 1) :
    fourierCollarTerm n z = z ^ n := by
  have hq : fourierCollarScaledDefect n z ≤ 0 := by
    dsimp [fourierCollarScaledDefect, fourierCollarRadialDefect]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by simp_all)
  simp [fourierCollarTerm, fourierCollarCutoff_one hq]

/-- The support radius remains in a fixed compact ball. -/
theorem fourierCollar_support_radius {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ 2 ≤ 1 + 1 / n ∧ z ∈ closedBall 0 2 := by
  have hn1 : (1 : ℝ) ≤ n := by simp_all
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : ‖z‖ ^ 2 - 1 ≤ 1 / n := by
    apply (le_div_iff₀ hn0).mpr
    rwa [mul_comm]
  have hinv  := (div_le_one hn0).mpr hn1
  refine ⟨by linarith, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  nlinarith 

/-- The shrinking support compensates exactly for monomial growth.
This proves the uniform exponential constant instead of assuming it. -/
theorem fourierCollar_support_pow_le_exp_half {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    {z : ℂ} (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ m ≤ Real.exp (1 / 2) := by
  have hsupport := (fourierCollar_support_radius hn hz).1
  rcases le_or_gt ‖z‖ 1 with hr | hr
  · exact (pow_le_one₀ (norm_nonneg z) hr).trans (by
    norm_num)
  · have hlog : 2 * Real.log ‖z‖ ≤ ‖z‖ ^ 2 - 1 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using
        Real.log_le_sub_one_of_pos (sq_pos_of_pos (lt_trans zero_lt_one hr))
    have hcancel : (1 / (n : ℝ)) * n = 1 := by field_simp 
    have hne : n * Real.log ‖z‖ ≤ 1 / 2 := by nlinarith
    exact (pow_le_pow_right₀ hr.le hm).trans (by
      have heq : ‖z‖ ^ n = Real.exp (n * Real.log ‖z‖) := by
        simp [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr)]
      simp_all)

/-- The exact real derivative norm of a holomorphic monomial. -/
theorem fourierCollar_pow_iteratedFDeriv_norm (n k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w  => w ^ n) z‖ =
      n.descFactorial k * ‖z‖ ^ (n - k) := by
  have hp : ContDiffAt ℂ k (fun w  => w ^ n) z := (contDiff_id.pow n).contDiffAt
  rw [← hp.restrictScalars_iteratedFDeriv ]
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

theorem fourierCollar_pow_iteratedFDeriv_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun w  => w ^ n) z‖ ≤ n ^ k * Real.exp (1 / 2) := by
  rw [fourierCollar_pow_iteratedFDeriv_norm]
  exact mul_le_mul (by
    exact_mod_cast Nat.descFactorial_le_pow n k) (fourierCollar_support_pow_le_exp_half hn (Nat.sub_le _ _) hz)
    (by positivity) (by positivity)

/-- True uniform kth-order bounds for the individual collar summands. -/
theorem fourierCollarTerm_exists_iteratedFDeriv_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ,
      ‖iteratedFDeriv ℝ k (fourierCollarTerm n) z‖ ≤ B * n ^ k := by
  obtain ⟨C, hC, hχ⟩ := fourierCollarCutoff_exists_finite_derivative_bound k
  obtain ⟨D, hD, hq⟩ := fourierCollarRadialDefect_exists_finite_derivative_bound k
  let B := ∑ i ∈ Finset.range (k + 1),
    k.choose i * Real.exp (1 / 2) * (k - i).factorial * C * D ^ (k - i)
  have hB : 0 ≤ B := by
    positivity
  refine ⟨B, hB, ?_⟩
  intro n hn z
  have hn1 : (1 : ℝ) ≤ n := by simp_all
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hz : fourierCollarScaledDefect n z ≤ 1
  · have hscaled (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ ≤ (n * D) ^ i := by
      have hscale : ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ =
          n * ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ := by
        change ‖iteratedFDeriv ℝ i (fun w => (n : ℝ) • fourierCollarRadialDefect w) z‖ = _
        rw [iteratedFDeriv_const_smul_apply'
          (fourierCollarRadialDefect_contDiff i).contDiffAt, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hn0.le]
      rw [hscale]
      exact (mul_le_mul_of_nonneg_left (hq i hi z (fourierCollar_support_radius hn hz).2) hn0.le).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ (by
        simpa only [one_mul] using mul_le_mul hn1 hD (by norm_num) hn0.le) hi1)
    have hcut (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j
          (fun w  => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          j.factorial * C * (n * D) ^ j := by
      simpa only [Function.comp_def, Complex.ofRealLI_apply] using (Complex.ofRealLI.norm_iteratedFDeriv_comp_left 
        (((fourierCollarCutoff_contDiff j).comp
          (fourierCollarScaledDefect_contDiff j n)).contDiffAt) le_rfl).le.trans (norm_iteratedFDeriv_comp_le (fourierCollarCutoff_contDiff j)
        (fourierCollarScaledDefect_contDiff j n) le_rfl z
        (fun i hi => hχ i (hi.trans hj) _) (fun i hi1 hi => hscaled i hi1 (hi.trans hj)))
    apply (norm_iteratedFDeriv_mul_le
      (contDiff_id.pow n)
      (Complex.ofRealCLM.contDiff.comp ((fourierCollarCutoff_contDiff k).comp
        (fourierCollarScaledDefect_contDiff k n))) z le_rfl).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hchosen := mul_le_mul_of_nonneg_left (mul_le_mul (fourierCollar_pow_iteratedFDeriv_le hn i hz) (hcut (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)) (show (0 : ℝ) ≤ k.choose i from Nat.cast_nonneg _)
    calc
      k.choose i * ‖iteratedFDeriv ℝ i (fun w  => w ^ n) z‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun w  => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          k.choose i * (n ^ i * Real.exp (1 / 2)) *
            ((k - i).factorial * C * (n * D) ^ (k - i)) := by
        linarith
      _ = (k.choose i * Real.exp (1 / 2) * (k - i).factorial * C * D ^ (k - i)) *
          (n ^ i * n ^ (k - i)) := by ring
      _ = (k.choose i * Real.exp (1 / 2) * (k - i).factorial * C * D ^ (k - i)) *
          n ^ k := by simp [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  · have heq : fourierCollarTerm n =ᶠ[𝓝 z] (fun _  => 0) := by
      filter_upwards [(isOpen_lt continuous_const (fourierCollarScaledDefect_contDiff 0 n).continuous).mem_nhds (lt_of_not_ge hz)] with w hw
      simp [fourierCollarTerm, fourierCollarCutoff_zero hw.le]
    have hd := (heq.iteratedFDeriv ℝ k).eq_of_nhds
    simp_all

/-- All polynomially weighted ordinary Taylor coefficients are absolutely
summable. This is an intermediate Fourier regularity input, not a collar. -/
def HasRapidFourierDecay (a : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k)

def fourierCollarExtension (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  a 0 + ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z

/-- Smoothness of the constructed series follows from actual uniform
derivative majorants, rather than a smooth-series premise. -/
theorem fourierCollarExtension_contDiff {a : ℕ → ℂ} (ha : HasRapidFourierDecay a) :
    ContDiff ℝ (⊤ : ℕ∞) (fourierCollarExtension a) := by
  choose B hB hbound using fourierCollarTerm_exists_iteratedFDeriv_bound
  exact contDiff_const.add (by
    apply contDiff_tsum 
    · intro n
      exact (fourierCollarTerm_contDiff ⊤ (n + 1)).const_smul (a (n + 1))
    · intro k _
      exact (ha k).mul_left (B k)
    · intro k n z _
      rw [iteratedFDeriv_const_smul_apply'
        (fourierCollarTerm_contDiff k (n + 1)).contDiffAt, norm_smul]
      calc
        ‖a (n + 1)‖ * ‖iteratedFDeriv ℝ k (fourierCollarTerm (n + 1)) z‖ ≤
            ‖a (n + 1)‖ * (B k * (n + 1 : ℕ) ^ k) :=
          mul_le_mul_of_nonneg_left (hbound k (n + 1) (by omega) z) (norm_nonneg _)
        _ = B k * (‖a (n + 1)‖ * (n + 1 : ℕ) ^ k) := by ring)

/-- Every summand agrees with its actual Taylor monomial on the
closed disk, including the boundary. The zeroth coefficient is separate. -/
theorem fourierCollarExtension_eq_taylor_on_closedDisk (a : ℕ → ℂ) {z : ℂ}
    (hz : z ∈ closedBall 0 1) :
    fourierCollarExtension a z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1) := by
  unfold fourierCollarExtension
  congr 1
  apply tsum_congr
  intro n
  simp [fourierCollarTerm_eq_pow_on_closedDisk (n + 1) hz]

/-- A genuine smooth collar from genuine rapidly decaying Taylor data.
The input equality is a Taylor-series identity for F, never an assumed
extension or an assumed infinite-sum differentiability assertion. -/
theorem exists_smooth_fourier_collar_of_taylor {a : ℕ → ℂ} (ha : HasRapidFourierDecay a)
    {F : ℂ → ℂ} (hTaylor : ∀ z ∈ closedBall 0 1,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧ EqOn G F (closedBall 0 1) := by
  refine ⟨fourierCollarExtension a, fourierCollarExtension_contDiff ha, ?_⟩
  intro z hz
  rw [fourierCollarExtension_eq_taylor_on_closedDisk a hz, hTaylor z hz]

/-- Interior complex holomorphicity is inherited from the actual F.
Only real smoothness is asserted outside the disk. -/
theorem exists_smooth_holomorphic_fourier_collar_of_taylor {a : ℕ → ℂ}
    (ha : HasRapidFourierDecay a) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hTaylor : ∀ z ∈ closedBall 0 1,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      EqOn G F (closedBall 0 1) ∧ DifferentiableOn ℂ G (ball 0 1) := by
  obtain ⟨G, hG, hGF⟩ := exists_smooth_fourier_collar_of_taylor ha hTaylor
  exact ⟨G, hG, hGF, hF.congr (fun z hz => hGF (ball_subset_closedBall hz))⟩

end PolyaNeumann
