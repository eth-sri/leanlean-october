module
public import CenteredDilatedReflection
public import GuthMaynard.Improvement.SourceRatioHeightBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- Strict dyadic endpoints agree with shellEnergy's [H,2H) convention. -/
theorem strict_dyadic_prefix {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (height weight : ι → ℝ) {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    (∑ q ∈ S.filter (fun q => height q < (2:ℝ)^J*Y), weight q) =
      (∑ q ∈ S.filter (fun q => height q < Y), weight q) +
      ∑ j ∈ range J, ∑ q ∈ S.filter
        (fun q => (2:ℝ)^j*Y ≤ height q ∧ height q < (2:ℝ)^(j+1)*Y), weight q := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : (2:ℝ)^J*Y ≤ (2:ℝ)^(J+1)*Y := by
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) J) hY]
    have hlo : (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y)).filter
        (fun q => height q < (2:ℝ)^J*Y) = S.filter (fun q => height q < (2:ℝ)^J*Y) := by
      ext q
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hq,_⟩,hh⟩; exact ⟨hq,hh⟩
      · rintro ⟨hq,hh⟩; exact ⟨⟨hq,hh.trans_le hstep⟩,hh⟩
    have hhi : (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y)).filter
        (fun q => ¬height q < (2:ℝ)^J*Y) = S.filter
        (fun q => (2:ℝ)^J*Y ≤ height q ∧ height q < (2:ℝ)^(J+1)*Y) := by
      ext q
      simp only [mem_filter,not_lt]
      tauto
    have hh := sum_filter_add_sum_filter_not (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y))
      (fun q => height q < (2:ℝ)^J*Y) weight
    rw [hlo,hhi] at hh
    rw [← hh,ih,sum_range_succ]
    ring

/-- The actual least dyadic cover has only a logarithmic number of shells.
The factor 8 in the reflected-length assumption below is recorded explicitly. -/
theorem reflection_shell_count {T L : ℝ} (hT : 1 < T) (hL : 1 ≤ L)
    (hY : Real.pi*L/8 ≤ T) :
    ∃ J : ℕ, T < (2:ℝ)^J*(Real.pi*L/8) ∧
      (∀ j < J, (2:ℝ)^j*(Real.pi*L/8) < 2*T) ∧
      (J:ℝ) ≤ 4+Real.log T/Real.log 2 := by
  have hLp : 0 < L := by linarith
  have hYp : 0 < Real.pi*L/8 := by positivity
  obtain ⟨J,hcover,hmin,_,_⟩ := GuthMaynard.Improvement.source_least_height_cover hYp
    (show Real.pi*L/8 ≤ 2*T by linarith)
  refine ⟨J,lt_of_lt_of_le (by linarith) hcover,hmin,?_⟩
  cases hJ : J with
  | zero =>
    simp only [Nat.cast_zero]
    have hlT := Real.log_nonneg hT.le
    positivity
  | succ j =>
    have hh := hmin j (by omega)
    have hylo : 1/4 ≤ Real.pi*L/8 := by nlinarith [Real.pi_gt_three]
    have hp : (2:ℝ)^j < 8*T := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < (2:ℝ)^j) hp.le
    rw [Real.log_pow,show (8:ℝ)=2^3 by norm_num,Real.log_mul (by norm_num) (by linarith),
      Real.log_pow] at hlog
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hj : (j:ℝ) ≤ 3+Real.log T/Real.log 2 := by
      calc
        _ ≤ (3*Real.log 2+Real.log T)/Real.log 2 := (le_div_iff₀ htwo).mpr (by simpa using hlog)
        _ = _ := by field_simp
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

/-- A squared cutoff is still an actual smooth reflection cutoff. -/
def reflectionSquare (w : MathCollab.Density.ReflectionCutoff) :
    MathCollab.Density.ReflectionCutoff where
  toFun x := (w x)^2
  smooth := w.smooth.pow 2
  support := by
    apply subset_trans (closure_mono ?_) w.support
    intro x hx
    change (w x)^2 ≠ 0 at hx
    change w x ≠ 0
    intro hz
    exact hx (by rw [hz]; norm_num)

/-- The literal discrete Gram matrix with the published squared cutoff. -/
def cutoffGramMatrix (w : MathCollab.Density.ReflectionCutoff) (L : ℝ) (W : Finset ℝ) :
    Matrix W W ℂ := fun t u => ∑' n : ℕ,
      (((w ((n:ℝ)/L))^2:ℝ):ℂ)*MathCollab.Density.dirichletPhase ((n:ℝ)/L) (t-u)

/-- The continuous term is kept independently of the discrete Gram sum. -/
def cutoffContinuousMatrix (w : MathCollab.Density.ReflectionCutoff) (L : ℝ) (W : Finset ℝ) :
    Matrix W W ℂ := fun t u => (L:ℂ)*
      MathCollab.Density.cutoffIntegral (reflectionSquare w) (t-u)

def cutoffCenteredMatrix (w : MathCollab.Density.ReflectionCutoff) (L : ℝ) (W : Finset ℝ) :
    Matrix W W ℂ := cutoffGramMatrix w L W-cutoffContinuousMatrix w L W

theorem cutoff_centered_entry (w : MathCollab.Density.ReflectionCutoff) (L : ℝ)
    (W : Finset ℝ) (t u : W) :
    cutoffCenteredMatrix w L W t u =
      MathCollab.Density.hKernel (reflectionSquare w) L (t-u) := rfl

theorem cutoff_centered_hermitian (w : MathCollab.Density.ReflectionCutoff) (L : ℝ)
    (W : Finset ℝ) : (cutoffCenteredMatrix w L W).IsHermitian := by
  ext t u
  simp only [Matrix.conjTranspose_apply,cutoff_centered_entry]
  rw [show (u:ℝ)-t = -((t:ℝ)-u) by ring,MathCollab.Density.hKernel_neg]
  simp

/-- The signed second trace is exactly the finite centered-kernel energy. -/
theorem cutoff_centered_trace_identity (w : MathCollab.Density.ReflectionCutoff) (L : ℝ)
    (W : Finset ℝ) :
    Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W) =
      ((∑ t ∈ W, ∑ u ∈ W,
        ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2:ℝ):ℂ) := by
  let H := cutoffCenteredMatrix w L W
  have hh : H.conjTranspose=H := cutoff_centered_hermitian w L W
  change Matrix.trace (H*H) = _
  nth_rw 2 [← hh]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have he (t u : W) : H t u*star (H t u) = ((‖H t u‖^2:ℝ):ℂ) := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.mul_conj' (H t u)
  simp_rw [he]
  simp only [H,cutoff_centered_entry,Complex.ofReal_sum]
  rw [Finset.sum_coe_sort W (fun t => ∑ u : W,
    ((‖MathCollab.Density.hKernel (reflectionSquare w) L (t-(u:ℝ))‖^2:ℝ):ℂ))]
  apply sum_congr rfl
  intro t _
  exact Finset.sum_coe_sort W (fun u =>
    ((‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2:ℝ):ℂ))


