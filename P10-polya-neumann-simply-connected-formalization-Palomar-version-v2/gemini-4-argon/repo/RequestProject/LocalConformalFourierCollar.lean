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


noncomputable section

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology ContDiff

/-- The actual transition, with precisely the required two constant sides. -/
def fourierCollarCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

theorem fourierCollarCutoff_one  (ht : t ≤ 0) : fourierCollarCutoff t = 1 := by
  simp [fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos ht]

theorem fourierCollarCutoff_zero  (ht : 1 ≤ t) : fourierCollarCutoff t = 0 := by
  simp [fourierCollarCutoff, Real.smoothTransition.one_of_one_le ht]

theorem fourierCollarCutoff_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

/-- Each derivative is truly bounded globally: outside the compact
transition interval the function is locally constant. -/
theorem fourierCollarCutoff_exists_derivative_bound i :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv' (fourierCollarCutoff_contDiff (i : ℕ∞))).continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc 0 1
  · exact (hB t ht).trans (le_max_right _ _)
  · rcases lt_or_ge t 0 with ht0 | ht0
    · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ => 1) := by
        filter_upwards [eventually_lt_nhds ht0] with s hs
        exact fourierCollarCutoff_one hs.le
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      cases i with
      | zero => simpa using le_max_left 1 B
      | succ i =>
          simpa [iteratedFDeriv_succ_const] using
            (show 0 ≤ max 1 B by positivity)
    · have ht1 : 1 < t := lt_of_not_ge (fun h => ht ⟨ht0, h⟩)
      rw [((show fourierCollarCutoff =ᶠ[𝓝 t] (fun _ => 0) by
        filter_upwards [eventually_gt_nhds ht1] with s hs
        exact fourierCollarCutoff_zero hs.le).iteratedFDeriv ℝ i).eq_of_nhds]
      simpa [iteratedFDeriv_zero_fun] using
        show 0 ≤ max 1 B by positivity

def fourierCollarRadialDefect (z : ℂ) : ℝ := ‖z‖ ^ 2 - 1

theorem fourierCollarRadialDefect_contDiff N : ContDiff ℝ N fourierCollarRadialDefect :=
  (contDiff_norm_sq ℂ).sub contDiff_const

def fourierCollarScaledDefect (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * fourierCollarRadialDefect z

theorem fourierCollarScaledDefect_contDiff N n :
    ContDiff ℝ N (fourierCollarScaledDefect n) :=
  contDiff_const.mul (fourierCollarRadialDefect_contDiff N)

def fourierCollarTerm (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n * (fourierCollarCutoff (fourierCollarScaledDefect n z) : ℂ)

theorem fourierCollarTerm_contDiff (N : ℕ∞) n : ContDiff ℝ N (fourierCollarTerm n) :=
  (contDiff_id.pow n).mul (Complex.ofRealCLM.contDiff.comp
    ((fourierCollarCutoff_contDiff N).comp (fourierCollarScaledDefect_contDiff N n)))

/-- The support radius remains in a fixed compact ball. -/
theorem fourierCollar_support_radius  (hn : 1 ≤ n) 
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ 2 ≤ 1 + 1 / (n : ℝ) ∧ z ∈ closedBall 0 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : ‖z‖ ^ 2 - 1 ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    change (‖z‖ ^ 2 - 1) * (n : ℝ) ≤ 1
    rw [mul_comm]
    exact hz
  have hinv := (div_le_one hn0).mpr hn1
  refine ⟨by linarith, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg z]

/-- The shrinking support compensates exactly for monomial growth.
This proves the uniform exponential constant instead of assuming it. -/
theorem fourierCollar_support_pow_le_exp_half {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
     (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ m ≤ Real.exp (1 / 2) := by
  have hsupport := (fourierCollar_support_radius hn hz).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rcases le_or_gt ‖z‖ 1 with hr | hr
  · exact (pow_le_one₀ (norm_nonneg z) hr).trans (by
    have h := Real.add_one_le_exp (1 / 2)
    linarith)
  · have hlog : (2 : ℝ) * Real.log ‖z‖ ≤ ‖z‖ ^ 2 - 1 := by
      simpa using
        Real.log_le_sub_one_of_pos (sq_pos_of_pos (lt_trans zero_lt_one hr))
    have hmul := mul_le_mul_of_nonneg_right (show 2 * Real.log ‖z‖ ≤ 1 / (n : ℝ) by linarith) hn0.le
    rw [show 1 / (n : ℝ) * (n : ℝ) = 1 by field_simp [hn0.ne']] at hmul
    exact (pow_le_pow_right₀ hr.le hm).trans (show ‖z‖ ^ n ≤ Real.exp (1 / 2) by
      rw [show ‖z‖ ^ n = Real.exp (n * Real.log ‖z‖) by
        rw [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr)]]
      exact Real.exp_le_exp.mpr (by nlinarith))

/-- The exact real derivative norm of a holomorphic monomial. -/
theorem fourierCollar_pow_iteratedFDeriv_norm n k z :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n) z‖ =
      (n.descFactorial k : ℝ) * ‖z‖ ^ (n - k) := by
  have hp : ContDiffAt ℂ k (fun w => w ^ n) z := (contDiff_id.pow n).contDiffAt
  rw [← hp.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Complex.norm_natCast]

/-- True uniform kth-order bounds for the individual collar summands. -/
theorem fourierCollarTerm_exists_iteratedFDeriv_bound k :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ,
      ‖iteratedFDeriv ℝ k (fourierCollarTerm n) z‖ ≤ B * (n : ℝ) ^ k := by
  obtain ⟨C, hC, hχ⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ C := by
    choose B hB hbound using fourierCollarCutoff_exists_derivative_bound
    let C := max 1 (∑ i ∈ Finset.range (k + 1), B i)
    refine ⟨C, le_max_left _ _, ?_⟩
    intro i hi t
    exact (hbound i t).trans ((Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))
  obtain ⟨D, hD, hq⟩ : ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ k, ∀ z ∈ closedBall 0 2, ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ D := by
    have hbound i : ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ closedBall 0 2,
        ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ B := by
      obtain ⟨B, hB⟩ := (isCompact_closedBall 0 2).exists_bound_of_continuousOn
        (ContDiff.continuous_iteratedFDeriv' (fourierCollarRadialDefect_contDiff i)).continuousOn
      exact ⟨max 1 B, le_max_left _ _, fun z hz => (hB z hz).trans (le_max_right _ _)⟩
    choose B hB hbound using hbound
    let D := max 1 (∑ i ∈ Finset.range (k + 1), B i)
    refine ⟨D, le_max_left _ _, ?_⟩
    intro i hi z hz
    exact (hbound i z hz).trans ((Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))
  let B := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * (k - i).factorial * C * D ^ (k - i)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨B, hB, ?_⟩
  intro n hn z
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hz : fourierCollarScaledDefect n z ≤ 1
  · have hz2 := (fourierCollar_support_radius hn hz).2
    have hscaled (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ ≤ (n * D) ^ i := by
      rw [show ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ = (n : ℝ) * ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ by
        change ‖iteratedFDeriv ℝ i (fun w => (n : ℝ) • fourierCollarRadialDefect w) z‖ = _
        rw [iteratedFDeriv_const_smul_apply'
          (fourierCollarRadialDefect_contDiff (i : ℕ∞)).contDiffAt, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hn0.le]]
      have hND : 1 ≤ (n : ℝ) * D := by
        simpa using mul_le_mul hn1 hD (by norm_num : (0 : ℝ) ≤ 1) hn0.le
      exact (mul_le_mul_of_nonneg_left (hq i hi z hz2) hn0.le).trans
        (by simpa using pow_le_pow_right₀ hND hi1)
    have hcut j (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j
          (fun w => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          j.factorial * C * (n * D) ^ j := by
      simpa [Function.comp_def] using (Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := z) (((fourierCollarCutoff_contDiff j).comp (fourierCollarScaledDefect_contDiff j n)).contDiffAt) le_rfl).le.trans (norm_iteratedFDeriv_comp_le (fourierCollarCutoff_contDiff j) (fourierCollarScaledDefect_contDiff j n) le_rfl z (fun i hi => hχ i (hi.trans hj) _) (fun i hi1 hi => hscaled i hi1 (hi.trans hj)))
    have hprod := norm_iteratedFDeriv_mul_le
      (contDiff_id.pow n)
      (Complex.ofRealCLM.contDiff.comp ((fourierCollarCutoff_contDiff k).comp
        (fourierCollarScaledDefect_contDiff k n))) z le_rfl
    change ‖iteratedFDeriv ℝ k (fun w => w ^ n *
      (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤ _
    apply hprod.trans
    rw [(rfl : B = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hmul := mul_le_mul (show ‖iteratedFDeriv ℝ i (fun w : ℂ => w ^ n) z‖ ≤ (n : ℝ) ^ i * Real.exp (1 / 2 : ℝ) by
      rw [fourierCollar_pow_iteratedFDeriv_norm]
      exact mul_le_mul (by
        exact_mod_cast Nat.descFactorial_le_pow n i) (fourierCollar_support_pow_le_exp_half hn (Nat.sub_le _ _) hz)
        (by positivity) (by positivity)) (hcut (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    calc
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => w ^ n) z‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun w => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          (k.choose i : ℝ) * (n ^ i * Real.exp (1 / 2 : ℝ)) *
            (((k - i).factorial : ℝ) * C * (n * D) ^ (k - i)) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
      _ = (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i) *
          (n ^ i * n ^ (k - i)) := by rw [mul_pow]; ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  · have hgt := lt_of_not_ge hz
    rw [((show fourierCollarTerm n =ᶠ[𝓝 z] (fun _ : ℂ => 0) by
      filter_upwards [(isOpen_lt continuous_const (fourierCollarScaledDefect_contDiff 0 n).continuous).mem_nhds hgt] with w hw
      simp [fourierCollarTerm, fourierCollarCutoff_zero hw.le]).iteratedFDeriv ℝ k).eq_of_nhds]
    simp [iteratedFDeriv_zero_fun]
    exact mul_nonneg hB (pow_nonneg hn0.le _)

/-- All polynomially weighted ordinary Taylor coefficients are absolutely
summable. This is an intermediate Fourier regularity input, not a collar. -/
def HasRapidFourierDecay (a : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k)

def fourierCollarExtension (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  a 0 + ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z

/-- Smoothness of the constructed series follows from actual uniform
derivative majorants, rather than a smooth-series premise. -/
theorem fourierCollarExtension_contDiff {a : ℕ → ℂ} (ha : HasRapidFourierDecay a) :
    ContDiff ℝ ∞ (fourierCollarExtension a) := by
  choose B hB hbound using fourierCollarTerm_exists_iteratedFDeriv_bound
  exact contDiff_const.add (by
    apply contDiff_tsum (v := fun k n => B k * (‖a (n + 1)‖ * (n + 1 : ℕ) ^ k))
    · intro n
      exact (fourierCollarTerm_contDiff ⊤ (n + 1)).const_smul (a (n + 1))
    · intro k _
      exact (ha k).mul_left (B k)
    · intro k n z _
      rw [iteratedFDeriv_const_smul_apply'
        (fourierCollarTerm_contDiff k (n + 1)).contDiffAt, norm_smul]
      calc
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left (hbound k (n + 1) (by omega) z) (norm_nonneg _)
        _ = _ := by ring)

/-- Every summand agrees with its actual Taylor monomial on the
closed disk, including the boundary. The zeroth coefficient is separate. -/
theorem fourierCollarExtension_eq_taylor_on_closedDisk a 
    (hz : z ∈ closedBall 0 1) :
    fourierCollarExtension a z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1) := by
  unfold fourierCollarExtension
  congr 1
  apply tsum_congr
  intro n
  rw [show fourierCollarTerm (n + 1) z = z ^ (n + 1) by
    have hr : ‖z‖ ≤ 1 := by simpa using hz
    simp [fourierCollarTerm, fourierCollarCutoff_one (show fourierCollarScaledDefect (n + 1) z ≤ 0 by
      dsimp [fourierCollarScaledDefect, fourierCollarRadialDefect]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by nlinarith [norm_nonneg z]))]]
  rfl

/-- Interior complex holomorphicity is inherited from the actual F.
Only real smoothness is asserted outside the disk. -/
theorem exists_smooth_holomorphic_fourier_collar_of_taylor 
    (ha : HasRapidFourierDecay a) 
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hTaylor : ∀ z ∈ closedBall 0 1,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧
      EqOn G F (closedBall 0 1) ∧ DifferentiableOn ℂ G (ball 0 1) := by
  obtain ⟨G, hG, hGF⟩ : ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧ EqOn G F (closedBall 0 1) := by
    refine ⟨fourierCollarExtension a, fourierCollarExtension_contDiff ha, ?_⟩
    intro z hz
    rw [fourierCollarExtension_eq_taylor_on_closedDisk a hz, hTaylor z hz]
  exact ⟨G, hG, hGF, hF.congr (fun z hz => hGF (ball_subset_closedBall hz))⟩

end PolyaNeumann
